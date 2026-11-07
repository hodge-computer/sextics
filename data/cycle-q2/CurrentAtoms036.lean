import Proposal.CurrentAtoms035

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a11008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11001 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11007 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11004 ^ 1)
theorem ha11008 : a11008.IsHomogeneous 36 := by
  unfold a11008
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11004.pow 1)))

@[irreducible]
def a11009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11003 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11008 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11006 ^ 1)
theorem ha11009 : a11009.IsHomogeneous 36 := by
  unfold a11009
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11006.pow 1)))

@[irreducible]
def a11010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00506 ^ 1)
theorem ha11010 : a11010.IsHomogeneous 24 := by
  unfold a11010
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a01327 ^ 1)
theorem ha11011 : a11011.IsHomogeneous 18 := by
  unfold a11011
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11010 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11011 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11000 ^ 1)
theorem ha11012 : a11012.IsHomogeneous 30 := by
  unfold a11012
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11010.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11011.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11000.pow 1)))

@[irreducible]
def a11013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a02935 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a02935 ^ 1)
theorem ha11013 : a11013.IsHomogeneous 24 := by
  unfold a11013
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11013 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11011 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11002 ^ 1)
theorem ha11014 : a11014.IsHomogeneous 30 := by
  unfold a11014
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11013.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11011.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11002.pow 1)))

@[irreducible]
def a11015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11012 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11014 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11003 ^ 1)
theorem ha11015 : a11015.IsHomogeneous 36 := by
  unfold a11015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11012.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11014.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11003.pow 1)))

@[irreducible]
def a11016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00155 ^ 1)
theorem ha11016 : a11016.IsHomogeneous 18 := by
  unfold a11016
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a11017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11010 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11005 ^ 1)
theorem ha11017 : a11017.IsHomogeneous 24 := by
  unfold a11017
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11016.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11010.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11005.pow 1)))

@[irreducible]
def a11018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11012 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11006 ^ 1)
theorem ha11018 : a11018.IsHomogeneous 30 := by
  unfold a11018
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11017.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11012.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11006.pow 1)))

@[irreducible]
def a11019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11018 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11015 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11009 ^ 1)
theorem ha11019 : a11019.IsHomogeneous 36 := by
  unfold a11019
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11015.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11009.pow 1)))

@[irreducible]
def a11020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00520 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00520 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01356 ^ 1)
theorem ha11020 : a11020.IsHomogeneous 18 := by
  unfold a11020
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00520.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01356.pow 1)))

@[irreducible]
def a11021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a02985 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01356 ^ 1)
theorem ha11021 : a11021.IsHomogeneous 24 := by
  unfold a11021
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha02985.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11021 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11020 ^ 1)
theorem ha11022 : a11022.IsHomogeneous 24 := by
  unfold a11022
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11021.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11020.pow 1)))

@[irreducible]
def a11023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00520 ^ 1)
theorem ha11023 : a11023.IsHomogeneous 12 := by
  unfold a11023
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00520.pow 1)))

@[irreducible]
def a11024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11005 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11023 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11020 ^ 1)
theorem ha11024 : a11024.IsHomogeneous 18 := by
  unfold a11024
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11005.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11023.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11020.pow 1)))

@[irreducible]
def a11025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11006 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a11022 ^ 1)
theorem ha11025 : a11025.IsHomogeneous 24 := by
  unfold a11025
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11006.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha11022.pow 1)))

@[irreducible]
def a11026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a02985 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02985 ^ 1)
theorem ha11026 : a11026.IsHomogeneous 30 := by
  unfold a11026
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a11027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11007 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11021 ^ 1)
theorem ha11027 : a11027.IsHomogeneous 36 := by
  unfold a11027
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11021.pow 1)))

@[irreducible]
def a11028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11008 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11027 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11022 ^ 1)
theorem ha11028 : a11028.IsHomogeneous 36 := by
  unfold a11028
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11027.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11022.pow 1)))

@[irreducible]
def a11029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11028 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11025 ^ 1)
theorem ha11029 : a11029.IsHomogeneous 36 := by
  unfold a11029
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11028.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11025.pow 1)))

@[irreducible]
def a11030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha11030 : a11030.IsHomogeneous 12 := by
  unfold a11030
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a11031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11016 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11030 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11023 ^ 1)
theorem ha11031 : a11031.IsHomogeneous 18 := by
  unfold a11031
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11030.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11023.pow 1)))

@[irreducible]
def a11032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11017 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11024 ^ 1)
theorem ha11032 : a11032.IsHomogeneous 24 := by
  unfold a11032
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11017.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11024.pow 1)))

@[irreducible]
def a11033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11018 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11025 ^ 1)
theorem ha11033 : a11033.IsHomogeneous 30 := by
  unfold a11033
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11018.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11025.pow 1)))

@[irreducible]
def a11034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11019 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11029 ^ 1)
theorem ha11034 : a11034.IsHomogeneous 36 := by
  unfold a11034
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11033.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11019.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11029.pow 1)))

@[irreducible]
def a11035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00520 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00025 ^ 1 * a01327 ^ 1 * a01356 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1 * a01327 ^ 1)
theorem ha11035 : a11035.IsHomogeneous 30 := by
  unfold a11035
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a02985 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1 * a01356 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01356 ^ 1)
theorem ha11036 : a11036.IsHomogeneous 36 := by
  unfold a11036
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha02985.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11001 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11036 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a11035 ^ 1)
theorem ha11037 : a11037.IsHomogeneous 36 := by
  unfold a11037
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11036.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha11035.pow 1)))

@[irreducible]
def a11038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a05754 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02935 ^ 1)
theorem ha11038 : a11038.IsHomogeneous 24 := by
  unfold a11038
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11002 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a11038 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11035 ^ 1)
theorem ha11039 : a11039.IsHomogeneous 30 := by
  unfold a11039
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11002.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha11038.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11035.pow 1)))

@[irreducible]
def a11040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11003 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11037 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11039 ^ 1)
theorem ha11040 : a11040.IsHomogeneous 36 := by
  unfold a11040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11037.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11039.pow 1)))

@[irreducible]
def a11041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a05834 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a02985 ^ 1)
theorem ha11041 : a11041.IsHomogeneous 36 := by
  unfold a11041
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha05834.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a11042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11036 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11041 ^ 1)
theorem ha11042 : a11042.IsHomogeneous 36 := by
  unfold a11042
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11036.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11041.pow 1)))

@[irreducible]
def a11043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11037 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11042 ^ 1)
theorem ha11043 : a11043.IsHomogeneous 36 := by
  unfold a11043
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11037.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11042.pow 1)))

@[irreducible]
def a11044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11040 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11043 ^ 1)
theorem ha11044 : a11044.IsHomogeneous 36 := by
  unfold a11044
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11040.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11043.pow 1)))

@[irreducible]
def a11045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a10779 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a05754 ^ 1)
theorem ha11045 : a11045.IsHomogeneous 24 := by
  unfold a11045
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha10779.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a11046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11013 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11045 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11038 ^ 1)
theorem ha11046 : a11046.IsHomogeneous 30 := by
  unfold a11046
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11013.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11045.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11038.pow 1)))

@[irreducible]
def a11047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11046 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11039 ^ 1)
theorem ha11047 : a11047.IsHomogeneous 36 := by
  unfold a11047
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11046.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11039.pow 1)))

@[irreducible]
def a11048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11015 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11047 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11040 ^ 1)
theorem ha11048 : a11048.IsHomogeneous 36 := by
  unfold a11048
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11015.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11047.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11040.pow 1)))

@[irreducible]
def a11049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11048 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11044 ^ 1)
theorem ha11049 : a11049.IsHomogeneous 36 := by
  unfold a11049
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11048.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11044.pow 1)))

@[irreducible]
def a11050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a05834 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05834 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a10897 ^ 1)
theorem ha11050 : a11050.IsHomogeneous 30 := by
  unfold a11050
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha10897.pow 1)))

@[irreducible]
def a11051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11026 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11050 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11041 ^ 1)
theorem ha11051 : a11051.IsHomogeneous 36 := by
  unfold a11051
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11026.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11050.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11041.pow 1)))

@[irreducible]
def a11052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11027 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11051 ^ 1)
theorem ha11052 : a11052.IsHomogeneous 36 := by
  unfold a11052
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11027.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11042.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11051.pow 1)))

@[irreducible]
def a11053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11043 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11052 ^ 1)
theorem ha11053 : a11053.IsHomogeneous 36 := by
  unfold a11053
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11043.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11052.pow 1)))

@[irreducible]
def a11054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11029 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11053 ^ 1)
theorem ha11054 : a11054.IsHomogeneous 36 := by
  unfold a11054
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11029.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11044.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11053.pow 1)))

@[irreducible]
def a11055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11034 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11049 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11054 ^ 1)
theorem ha11055 : a11055.IsHomogeneous 36 := by
  unfold a11055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11034.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11049.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11054.pow 1)))

@[irreducible]
def a11056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00316 ^ 1)
theorem ha11056 : a11056.IsHomogeneous 24 := by
  unfold a11056
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1 * a00547 ^ 1)
theorem ha11057 : a11057.IsHomogeneous 36 := by
  unfold a11057
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00864.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01412.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a00864 ^ 1)
theorem ha11058 : a11058.IsHomogeneous 36 := by
  unfold a11058
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11057 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11058 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11056 ^ 1)
theorem ha11059 : a11059.IsHomogeneous 36 := by
  unfold a11059
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11056.pow 1)))

@[irreducible]
def a11060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00547 ^ 1)
theorem ha11060 : a11060.IsHomogeneous 24 := by
  unfold a11060
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00168 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00547 ^ 1)
theorem ha11061 : a11061.IsHomogeneous 18 := by
  unfold a11061
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00547.pow 1)))

@[irreducible]
def a11062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11056 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11060 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11061 ^ 1)
theorem ha11062 : a11062.IsHomogeneous 24 := by
  unfold a11062
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11060.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11061.pow 1)))

@[irreducible]
def a11063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a01412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1)
theorem ha11063 : a11063.IsHomogeneous 24 := by
  unfold a11063
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11057 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11063 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11060 ^ 1)
theorem ha11064 : a11064.IsHomogeneous 36 := by
  unfold a11064
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11057.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11063.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11060.pow 1)))

@[irreducible]
def a11065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11064 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11062 ^ 1)
theorem ha11065 : a11065.IsHomogeneous 36 := by
  unfold a11065
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11064.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11062.pow 1)))

@[irreducible]
def a11066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00168 ^ 1 * a00316 ^ 1)
theorem ha11066 : a11066.IsHomogeneous 18 := by
  unfold a11066
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00864.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00168.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a02007 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00864 ^ 1)
theorem ha11067 : a11067.IsHomogeneous 24 := by
  unfold a11067
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11067 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11066 ^ 1)
theorem ha11068 : a11068.IsHomogeneous 24 := by
  unfold a11068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11067.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11066.pow 1)))

@[irreducible]
def a11069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a02007 ^ 1)
theorem ha11069 : a11069.IsHomogeneous 30 := by
  unfold a11069
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11058 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11067 ^ 1)
theorem ha11070 : a11070.IsHomogeneous 36 := by
  unfold a11070
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11069.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11067.pow 1)))

@[irreducible]
def a11071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11059 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11070 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11068 ^ 1)
theorem ha11071 : a11071.IsHomogeneous 36 := by
  unfold a11071
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11070.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11068.pow 1)))

@[irreducible]
def a11072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00168 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00037 ^ 1)
theorem ha11072 : a11072.IsHomogeneous 12 := by
  unfold a11072
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a11073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11061 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11072 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11066 ^ 1)
theorem ha11073 : a11073.IsHomogeneous 18 := by
  unfold a11073
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11061.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11072.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11066.pow 1)))

@[irreducible]
def a11074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11062 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11068 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11073 ^ 1)
theorem ha11074 : a11074.IsHomogeneous 24 := by
  unfold a11074
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11062.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11068.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11073.pow 1)))

@[irreducible]
def a11075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11065 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11071 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11074 ^ 1)
theorem ha11075 : a11075.IsHomogeneous 36 := by
  unfold a11075
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11065.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11071.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11074.pow 1)))

@[irreducible]
def a11076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00547 ^ 1)
theorem ha11076 : a11076.IsHomogeneous 24 := by
  unfold a11076
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00547.pow 1)))

@[irreducible]
def a11077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03085 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01412 ^ 1)
theorem ha11077 : a11077.IsHomogeneous 18 := by
  unfold a11077
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03085.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01412.pow 1)))

@[irreducible]
def a11078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11076 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11077 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11060 ^ 1)
theorem ha11078 : a11078.IsHomogeneous 30 := by
  unfold a11078
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11076.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11077.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11060.pow 1)))

@[irreducible]
def a11079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00547 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00168 ^ 1)
theorem ha11079 : a11079.IsHomogeneous 18 := by
  unfold a11079
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00168.pow 1)))

@[irreducible]
def a11080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11076 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11061 ^ 1)
theorem ha11080 : a11080.IsHomogeneous 24 := by
  unfold a11080
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11076.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11061.pow 1)))

@[irreducible]
def a11081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11080 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11078 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11062 ^ 1)
theorem ha11081 : a11081.IsHomogeneous 30 := by
  unfold a11081
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11080.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11078.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11062.pow 1)))

@[irreducible]
def a11082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05994 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03085 ^ 1)
theorem ha11082 : a11082.IsHomogeneous 24 := by
  unfold a11082
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11082 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11063 ^ 1) + (C ((35 : ℂ) / (48 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11077 ^ 1)
theorem ha11083 : a11083.IsHomogeneous 30 := by
  unfold a11083
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11082.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11063.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (48 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11077.pow 1)))

@[irreducible]
def a11084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11078 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11083 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11064 ^ 1)
theorem ha11084 : a11084.IsHomogeneous 36 := by
  unfold a11084
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11078.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11083.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11064.pow 1)))

@[irreducible]
def a11085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11081 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11084 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11065 ^ 1)
theorem ha11085 : a11085.IsHomogeneous 36 := by
  unfold a11085
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11084.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11065.pow 1)))

@[irreducible]
def a11086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00037 ^ 1)
theorem ha11086 : a11086.IsHomogeneous 12 := by
  unfold a11086
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00037.pow 1)))

@[irreducible]
def a11087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11079 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11086 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11072 ^ 1)
theorem ha11087 : a11087.IsHomogeneous 18 := by
  unfold a11087
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11079.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11072.pow 1)))

@[irreducible]
def a11088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11080 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11073 ^ 1)
theorem ha11088 : a11088.IsHomogeneous 24 := by
  unfold a11088
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11087.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11080.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11073.pow 1)))

@[irreducible]
def a11089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11088 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11081 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11074 ^ 1)
theorem ha11089 : a11089.IsHomogeneous 30 := by
  unfold a11089
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11088.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11081.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11074.pow 1)))

@[irreducible]
def a11090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11089 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11085 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11075 ^ 1)
theorem ha11090 : a11090.IsHomogeneous 36 := by
  unfold a11090
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11089.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11085.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11075.pow 1)))

@[irreducible]
def a11091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00864 ^ 1 * a01412 ^ 1)
theorem ha11091 : a11091.IsHomogeneous 36 := by
  unfold a11091
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a03085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1 * a01412 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a01412 ^ 1)
theorem ha11092 : a11092.IsHomogeneous 30 := by
  unfold a11092
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01412.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11057 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11091 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a11092 ^ 1)
theorem ha11093 : a11093.IsHomogeneous 36 := by
  unfold a11093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11091.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha11092.pow 1)))

@[irreducible]
def a11094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02007 ^ 1)
theorem ha11094 : a11094.IsHomogeneous 36 := by
  unfold a11094
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11058 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11091 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11094 ^ 1)
theorem ha11095 : a11095.IsHomogeneous 36 := by
  unfold a11095
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11091.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11094.pow 1)))

@[irreducible]
def a11096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11093 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11095 ^ 1)
theorem ha11096 : a11096.IsHomogeneous 36 := by
  unfold a11096
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11093.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11095.pow 1)))

@[irreducible]
def a11097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a03085 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05994 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1)
theorem ha11097 : a11097.IsHomogeneous 24 := by
  unfold a11097
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05994.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11063 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11097 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11092 ^ 1)
theorem ha11098 : a11098.IsHomogeneous 30 := by
  unfold a11098
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11063.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11097.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11092.pow 1)))

@[irreducible]
def a11099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11064 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11093 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11098 ^ 1)
theorem ha11099 : a11099.IsHomogeneous 36 := by
  unfold a11099
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11064.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11093.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11098.pow 1)))

@[irreducible]
def a11100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11065 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11099 ^ 1)
theorem ha11100 : a11100.IsHomogeneous 36 := by
  unfold a11100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11065.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11096.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11099.pow 1)))

@[irreducible]
def a11101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a04085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a07557 ^ 1)
theorem ha11101 : a11101.IsHomogeneous 30 := by
  unfold a11101
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha07557.pow 1)))

@[irreducible]
def a11102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11069 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11101 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11094 ^ 1)
theorem ha11102 : a11102.IsHomogeneous 36 := by
  unfold a11102
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11069.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11101.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11094.pow 1)))

@[irreducible]
def a11103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11095 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11102 ^ 1)
theorem ha11103 : a11103.IsHomogeneous 36 := by
  unfold a11103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11095.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11102.pow 1)))

@[irreducible]
def a11104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11096 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11103 ^ 1)
theorem ha11104 : a11104.IsHomogeneous 36 := by
  unfold a11104
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11096.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11103.pow 1)))

@[irreducible]
def a11105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11075 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11104 ^ 1)
theorem ha11105 : a11105.IsHomogeneous 36 := by
  unfold a11105
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11075.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11100.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11104.pow 1)))

@[irreducible]
def a11106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha11106 : a11106.IsHomogeneous 12 := by
  unfold a11106
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a11107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01327 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a02935 ^ 1)
theorem ha11107 : a11107.IsHomogeneous 6 := by
  unfold a11107
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha02935.pow 1)))

@[irreducible]
def a11108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11106 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a11107 ^ 1)
theorem ha11108 : a11108.IsHomogeneous 12 := by
  unfold a11108
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11106.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha11107.pow 1)))

@[irreducible]
def a11109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha11109 : a11109.IsHomogeneous 12 := by
  unfold a11109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a11110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11106 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11109 ^ 1)
theorem ha11110 : a11110.IsHomogeneous 12 := by
  unfold a11110
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11109.pow 1)))

@[irreducible]
def a11111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11108 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11110 ^ 1)
theorem ha11111 : a11111.IsHomogeneous 12 := by
  unfold a11111
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11108.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11110.pow 1)))

@[irreducible]
def a11112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02935 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a05754 ^ 1)
theorem ha11112 : a11112.IsHomogeneous 6 := by
  unfold a11112
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha05754.pow 1)))

@[irreducible]
def a11113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11107 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a11112 ^ 1)
theorem ha11113 : a11113.IsHomogeneous 6 := by
  unfold a11113
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11107.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha11112.pow 1)))

@[irreducible]
def a11114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11108 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a11113 ^ 1)
theorem ha11114 : a11114.IsHomogeneous 12 := by
  unfold a11114
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11108.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha11113.pow 1)))

@[irreducible]
def a11115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11114 ^ 1)
theorem ha11115 : a11115.IsHomogeneous 12 := by
  unfold a11115
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11114.pow 1)))

@[irreducible]
def a11116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1)
theorem ha11116 : a11116.IsHomogeneous 6 := by
  unfold a11116
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a11117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11109 ^ 1)
theorem ha11117 : a11117.IsHomogeneous 12 := by
  unfold a11117
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11109.pow 1)))

@[irreducible]
def a11118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11110 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11117 ^ 1)
theorem ha11118 : a11118.IsHomogeneous 12 := by
  unfold a11118
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11117.pow 1)))

@[irreducible]
def a11119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11118 ^ 1)
theorem ha11119 : a11119.IsHomogeneous 12 := by
  unfold a11119
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11118.pow 1)))

@[irreducible]
def a11120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11119 ^ 1)
theorem ha11120 : a11120.IsHomogeneous 12 := by
  unfold a11120
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11119.pow 1)))

@[irreducible]
def a11121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a10779 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05754 ^ 1)
theorem ha11121 : a11121.IsHomogeneous 12 := by
  unfold a11121
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha10779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05754.pow 1)))

@[irreducible]
def a11122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11121 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11112 ^ 1)
theorem ha11122 : a11122.IsHomogeneous 12 := by
  unfold a11122
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11121.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11112.pow 1)))

@[irreducible]
def a11123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11122 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11113 ^ 1)
theorem ha11123 : a11123.IsHomogeneous 12 := by
  unfold a11123
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11113.pow 1)))

@[irreducible]
def a11124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11114 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11123 ^ 1)
theorem ha11124 : a11124.IsHomogeneous 12 := by
  unfold a11124
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11123.pow 1)))

@[irreducible]
def a11125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11124 ^ 1)
theorem ha11125 : a11125.IsHomogeneous 12 := by
  unfold a11125
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11124.pow 1)))

@[irreducible]
def a11126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11125 ^ 1)
theorem ha11126 : a11126.IsHomogeneous 12 := by
  unfold a11126
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11125.pow 1)))

@[irreducible]
def a11127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a05775 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a02949 ^ 1)
theorem ha11127 : a11127.IsHomogeneous 12 := by
  unfold a11127
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha02949.pow 1)))

@[irreducible]
def a11128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11127 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06034 ^ 1)
theorem ha11128 : a11128.IsHomogeneous 12 := by
  unfold a11128
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11127.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06034.pow 1)))

@[irreducible]
def a11129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11128 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06035 ^ 1)
theorem ha11129 : a11129.IsHomogeneous 12 := by
  unfold a11129
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11128.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06035.pow 1)))

@[irreducible]
def a11130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06036 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11129 ^ 1)
theorem ha11130 : a11130.IsHomogeneous 12 := by
  unfold a11130
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06036.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11129.pow 1)))

@[irreducible]
def a11131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a10809 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a05775 ^ 1)
theorem ha11131 : a11131.IsHomogeneous 12 := by
  unfold a11131
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha10809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha05775.pow 1)))

@[irreducible]
def a11132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11127 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11131 ^ 1)
theorem ha11132 : a11132.IsHomogeneous 12 := by
  unfold a11132
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11131.pow 1)))

@[irreducible]
def a11133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11132 ^ 1)
theorem ha11133 : a11133.IsHomogeneous 12 := by
  unfold a11133
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11128.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11132.pow 1)))

@[irreducible]
def a11134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11133 ^ 1)
theorem ha11134 : a11134.IsHomogeneous 12 := by
  unfold a11134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11133.pow 1)))

@[irreducible]
def a11135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11130 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11134 ^ 1)
theorem ha11135 : a11135.IsHomogeneous 12 := by
  unfold a11135
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11134.pow 1)))

@[irreducible]
def a11136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06039 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11130 ^ 1)
theorem ha11136 : a11136.IsHomogeneous 12 := by
  unfold a11136
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11130.pow 1)))

@[irreducible]
def a11137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11136 ^ 1)
theorem ha11137 : a11137.IsHomogeneous 12 := by
  unfold a11137
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11135.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11136.pow 1)))

@[irreducible]
def a11138 : Poly := (C ((-7 : ℂ) / (3 : ℂ)) * a11137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11126 ^ 1)
theorem ha11138 : a11138.IsHomogeneous 12 := by
  unfold a11138
  exact (((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (3 : ℂ))).mul (ha11137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11126.pow 1)))

@[irreducible]
def a11139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a11138 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05994 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a05994 ^ 1)
theorem ha11139 : a11139.IsHomogeneous 24 := by
  unfold a11139
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha11138.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha05994.pow 1)))

@[irreducible]
def a11140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11082 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11139 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11097 ^ 1)
theorem ha11140 : a11140.IsHomogeneous 30 := by
  unfold a11140
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11082.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11139.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11097.pow 1)))

@[irreducible]
def a11141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11140 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11098 ^ 1)
theorem ha11141 : a11141.IsHomogeneous 36 := by
  unfold a11141
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11140.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11098.pow 1)))

@[irreducible]
def a11142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11084 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a11141 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11099 ^ 1)
theorem ha11142 : a11142.IsHomogeneous 36 := by
  unfold a11142
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha11141.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11099.pow 1)))

@[irreducible]
def a11143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11142 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11100 ^ 1)
theorem ha11143 : a11143.IsHomogeneous 36 := by
  unfold a11143
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11142.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11100.pow 1)))

@[irreducible]
def a11144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11143 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a11105 ^ 1)
theorem ha11144 : a11144.IsHomogeneous 36 := by
  unfold a11144
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11090.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11143.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha11105.pow 1)))

@[irreducible]
def a11145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11055 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11144 ^ 1)
theorem ha11145 : a11145.IsHomogeneous 36 := by
  unfold a11145
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11144.pow 1)))

@[irreducible]
def a11146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00316 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00171 ^ 1 * a00316 ^ 1)
theorem ha11146 : a11146.IsHomogeneous 30 := by
  unfold a11146
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a01429 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00555 ^ 1 * a00864 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha11147 : a11147.IsHomogeneous 30 := by
  unfold a11147
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a11148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a00864 ^ 1)
theorem ha11148 : a11148.IsHomogeneous 36 := by
  unfold a11148
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11146 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11148 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11147 ^ 1)
theorem ha11149 : a11149.IsHomogeneous 36 := by
  unfold a11149
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11148.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11147.pow 1)))

@[irreducible]
def a11150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00555 ^ 1)
theorem ha11150 : a11150.IsHomogeneous 24 := by
  unfold a11150
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a11151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00555 ^ 1)
theorem ha11151 : a11151.IsHomogeneous 18 := by
  unfold a11151
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1)))

@[irreducible]
def a11152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11146 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11150 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11151 ^ 1)
theorem ha11152 : a11152.IsHomogeneous 30 := by
  unfold a11152
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11146.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11150.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11151.pow 1)))

@[irreducible]
def a11153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00316 ^ 1 * a01429 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha11153 : a11153.IsHomogeneous 24 := by
  unfold a11153
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11150 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11153 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a11147 ^ 1)
theorem ha11154 : a11154.IsHomogeneous 30 := by
  unfold a11154
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11150.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11153.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha11147.pow 1)))

@[irreducible]
def a11155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11149 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11154 ^ 1)
theorem ha11155 : a11155.IsHomogeneous 36 := by
  unfold a11155
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11149.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11154.pow 1)))

@[irreducible]
def a11156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00171 ^ 1 * a00316 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1)
theorem ha11156 : a11156.IsHomogeneous 18 := by
  unfold a11156
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00171.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00864 ^ 1)
theorem ha11157 : a11157.IsHomogeneous 30 := by
  unfold a11157
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11146 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11157 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11156 ^ 1)
theorem ha11158 : a11158.IsHomogeneous 30 := by
  unfold a11158
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11157.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11156.pow 1)))

@[irreducible]
def a11159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a02007 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02007 ^ 1)
theorem ha11159 : a11159.IsHomogeneous 30 := by
  unfold a11159
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11157 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11148 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11159 ^ 1)
theorem ha11160 : a11160.IsHomogeneous 36 := by
  unfold a11160
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11148.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11159.pow 1)))

@[irreducible]
def a11161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11149 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11160 ^ 1)
theorem ha11161 : a11161.IsHomogeneous 36 := by
  unfold a11161
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11149.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11160.pow 1)))

@[irreducible]
def a11162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1)
theorem ha11162 : a11162.IsHomogeneous 12 := by
  unfold a11162
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)))

@[irreducible]
def a11163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11151 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a11156 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11162 ^ 1)
theorem ha11163 : a11163.IsHomogeneous 18 := by
  unfold a11163
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11151.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha11156.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11162.pow 1)))

@[irreducible]
def a11164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11158 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11163 ^ 1)
theorem ha11164 : a11164.IsHomogeneous 30 := by
  unfold a11164
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11158.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11163.pow 1)))

@[irreducible]
def a11165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11164 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11161 ^ 1)
theorem ha11165 : a11165.IsHomogeneous 36 := by
  unfold a11165
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11155.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11161.pow 1)))

@[irreducible]
def a11166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00555 ^ 1)
theorem ha11166 : a11166.IsHomogeneous 18 := by
  unfold a11166
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01429.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1)))

@[irreducible]
def a11167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03116 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01429 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00324 ^ 1 * a01429 ^ 1)
theorem ha11167 : a11167.IsHomogeneous 24 := by
  unfold a11167
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11167 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11166 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11150 ^ 1)
theorem ha11168 : a11168.IsHomogeneous 30 := by
  unfold a11168
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11167.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11166.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11150.pow 1)))

@[irreducible]
def a11169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00555 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00171 ^ 1)
theorem ha11169 : a11169.IsHomogeneous 18 := by
  unfold a11169
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00171.pow 1)))

@[irreducible]
def a11170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11169 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11166 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11151 ^ 1)
theorem ha11170 : a11170.IsHomogeneous 24 := by
  unfold a11170
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11169.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11166.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11151.pow 1)))

@[irreducible]
def a11171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11152 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a11168 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11170 ^ 1)
theorem ha11171 : a11171.IsHomogeneous 30 := by
  unfold a11171
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha11168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11170.pow 1)))

@[irreducible]
def a11172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a03116 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03116 ^ 1)
theorem ha11172 : a11172.IsHomogeneous 24 := by
  unfold a11172
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a11173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11167 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11172 ^ 1) + (C ((15 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a11153 ^ 1)
theorem ha11173 : a11173.IsHomogeneous 30 := by
  unfold a11173
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11167.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11172.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha11153.pow 1)))

@[irreducible]
def a11174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11173 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11154 ^ 1)
theorem ha11174 : a11174.IsHomogeneous 36 := by
  unfold a11174
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11173.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11154.pow 1)))

@[irreducible]
def a11175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11155 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a11174 ^ 1)
theorem ha11175 : a11175.IsHomogeneous 36 := by
  unfold a11175
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11171.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11155.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha11174.pow 1)))

@[irreducible]
def a11176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha11176 : a11176.IsHomogeneous 12 := by
  unfold a11176
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a11177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11169 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11176 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11162 ^ 1)
theorem ha11177 : a11177.IsHomogeneous 18 := by
  unfold a11177
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11169.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11176.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11162.pow 1)))

@[irreducible]
def a11178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11170 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11163 ^ 1)
theorem ha11178 : a11178.IsHomogeneous 24 := by
  unfold a11178
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11177.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11170.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11163.pow 1)))

@[irreducible]
def a11179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11164 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11171 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11178 ^ 1)
theorem ha11179 : a11179.IsHomogeneous 30 := by
  unfold a11179
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11178.pow 1)))

@[irreducible]
def a11180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11165 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11175 ^ 1)
theorem ha11180 : a11180.IsHomogeneous 36 := by
  unfold a11180
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11165.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11175.pow 1)))

@[irreducible]
def a11181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00555 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00555 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00032 ^ 1 * a00864 ^ 1 * a01429 ^ 1)
theorem ha11181 : a11181.IsHomogeneous 30 := by
  unfold a11181
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00032.pow 1)).mul (ha00864.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00864 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a01429 ^ 1)
theorem ha11182 : a11182.IsHomogeneous 30 := by
  unfold a11182
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00864.pow 1)).mul (ha01429.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11147 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11182 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a11181 ^ 1)
theorem ha11183 : a11183.IsHomogeneous 30 := by
  unfold a11183
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11182.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha11181.pow 1)))

@[irreducible]
def a11184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a02007 ^ 1)
theorem ha11184 : a11184.IsHomogeneous 36 := by
  unfold a11184
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11184 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11181 ^ 1)
theorem ha11185 : a11185.IsHomogeneous 36 := by
  unfold a11185
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11184.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11181.pow 1)))

@[irreducible]
def a11186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11149 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11185 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11183 ^ 1)
theorem ha11186 : a11186.IsHomogeneous 36 := by
  unfold a11186
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11185.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11183.pow 1)))

@[irreducible]
def a11187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a03116 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06044 ^ 1)
theorem ha11187 : a11187.IsHomogeneous 24 := by
  unfold a11187
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06044.pow 1)))

@[irreducible]
def a11188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11153 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11187 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11182 ^ 1)
theorem ha11188 : a11188.IsHomogeneous 30 := by
  unfold a11188
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11153.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11187.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11182.pow 1)))

@[irreducible]
def a11189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11154 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a11183 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a11188 ^ 1)
theorem ha11189 : a11189.IsHomogeneous 30 := by
  unfold a11189
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha11183.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha11188.pow 1)))

@[irreducible]
def a11190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11186 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11189 ^ 1)
theorem ha11190 : a11190.IsHomogeneous 36 := by
  unfold a11190
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11186.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11189.pow 1)))

@[irreducible]
def a11191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a07557 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a04085 ^ 1)
theorem ha11191 : a11191.IsHomogeneous 30 := by
  unfold a11191
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha07557.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha04085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a11192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11159 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11184 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11191 ^ 1)
theorem ha11192 : a11192.IsHomogeneous 36 := by
  unfold a11192
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11184.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11191.pow 1)))

@[irreducible]
def a11193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11160 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11185 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a11192 ^ 1)
theorem ha11193 : a11193.IsHomogeneous 36 := by
  unfold a11193
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11160.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11185.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha11192.pow 1)))

@[irreducible]
def a11194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11161 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11186 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11193 ^ 1)
theorem ha11194 : a11194.IsHomogeneous 36 := by
  unfold a11194
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11161.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11186.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11193.pow 1)))

@[irreducible]
def a11195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11165 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11194 ^ 1)
theorem ha11195 : a11195.IsHomogeneous 36 := by
  unfold a11195
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11165.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11190.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11194.pow 1)))

@[irreducible]
def a11196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a01335 ^ 1)
theorem ha11196 : a11196.IsHomogeneous 6 := by
  unfold a11196
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha01335.pow 1)))

@[irreducible]
def a11197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02949 ^ 1)
theorem ha11197 : a11197.IsHomogeneous 6 := by
  unfold a11197
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02949.pow 1)))

@[irreducible]
def a11198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11196 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a11197 ^ 1)
theorem ha11198 : a11198.IsHomogeneous 6 := by
  unfold a11198
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha11197.pow 1)))

@[irreducible]
def a11199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha11199 : a11199.IsHomogeneous 12 := by
  unfold a11199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a11200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11199 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11196 ^ 1)
theorem ha11200 : a11200.IsHomogeneous 12 := by
  unfold a11200
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11199.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11196.pow 1)))

@[irreducible]
def a11201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11200 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11198 ^ 1)
theorem ha11201 : a11201.IsHomogeneous 12 := by
  unfold a11201
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11200.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11198.pow 1)))

@[irreducible]
def a11202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02949 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a05775 ^ 1)
theorem ha11202 : a11202.IsHomogeneous 6 := by
  unfold a11202
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha05775.pow 1)))

@[irreducible]
def a11203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11202 ^ 1)
theorem ha11203 : a11203.IsHomogeneous 6 := by
  unfold a11203
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11197.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11202.pow 1)))

@[irreducible]
def a11204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11198 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a11203 ^ 1)
theorem ha11204 : a11204.IsHomogeneous 6 := by
  unfold a11204
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha11203.pow 1)))

@[irreducible]
def a11205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11201 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11204 ^ 1)
theorem ha11205 : a11205.IsHomogeneous 12 := by
  unfold a11205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11204.pow 1)))

@[irreducible]
def a11206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11199 ^ 1)
theorem ha11206 : a11206.IsHomogeneous 12 := by
  unfold a11206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05762.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11199.pow 1)))

@[irreducible]
def a11207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11206 ^ 1)
theorem ha11207 : a11207.IsHomogeneous 12 := by
  unfold a11207
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11200.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11206.pow 1)))

@[irreducible]
def a11208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11207 ^ 1)
theorem ha11208 : a11208.IsHomogeneous 12 := by
  unfold a11208
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11201.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11207.pow 1)))

@[irreducible]
def a11209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11205 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11208 ^ 1)
theorem ha11209 : a11209.IsHomogeneous 12 := by
  unfold a11209
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11208.pow 1)))

@[irreducible]
def a11210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a10809 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05775 ^ 1)
theorem ha11210 : a11210.IsHomogeneous 12 := by
  unfold a11210
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha10809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05775.pow 1)))

@[irreducible]
def a11211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11210 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11202 ^ 1)
theorem ha11211 : a11211.IsHomogeneous 12 := by
  unfold a11211
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11210.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11202.pow 1)))

@[irreducible]
def a11212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11211 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11203 ^ 1)
theorem ha11212 : a11212.IsHomogeneous 12 := by
  unfold a11212
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11203.pow 1)))

@[irreducible]
def a11213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11212 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11204 ^ 1)
theorem ha11213 : a11213.IsHomogeneous 12 := by
  unfold a11213
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11212.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11204.pow 1)))

@[irreducible]
def a11214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11205 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11213 ^ 1)
theorem ha11214 : a11214.IsHomogeneous 12 := by
  unfold a11214
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11213.pow 1)))

@[irreducible]
def a11215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11214 ^ 1)
theorem ha11215 : a11215.IsHomogeneous 12 := by
  unfold a11215
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11214.pow 1)))

@[irreducible]
def a11216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a11215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a06044 ^ 1)
theorem ha11216 : a11216.IsHomogeneous 24 := by
  unfold a11216
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha11215.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha06044.pow 1)))

@[irreducible]
def a11217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11172 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11216 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11187 ^ 1)
theorem ha11217 : a11217.IsHomogeneous 30 := by
  unfold a11217
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11172.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11216.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11187.pow 1)))

@[irreducible]
def a11218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11173 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11217 ^ 1) + (C ((15 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a11188 ^ 1)
theorem ha11218 : a11218.IsHomogeneous 36 := by
  unfold a11218
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11217.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha11188.pow 1)))

@[irreducible]
def a11219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11218 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11189 ^ 1)
theorem ha11219 : a11219.IsHomogeneous 36 := by
  unfold a11219
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11174.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11218.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11189.pow 1)))

@[irreducible]
def a11220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11175 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11190 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a11219 ^ 1)
theorem ha11220 : a11220.IsHomogeneous 36 := by
  unfold a11220
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11190.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha11219.pow 1)))

@[irreducible]
def a11221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11195 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11220 ^ 1)
theorem ha11221 : a11221.IsHomogeneous 36 := by
  unfold a11221
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11180.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11195.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11220.pow 1)))

@[irreducible]
def a11222 : Poly := (C ((-7 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a11221 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10999 ^ 1) + (C ((7 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a11145 ^ 1)
theorem ha11222 : a11222.IsHomogeneous 49 := by
  unfold a11222
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha11221.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10999.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha11145.pow 1)))

@[irreducible]
def a11223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a03016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1 * a01373 ^ 1)
theorem ha11223 : a11223.IsHomogeneous 36 := by
  unfold a11223
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a11224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00528 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00864 ^ 1 * a01373 ^ 1)
theorem ha11224 : a11224.IsHomogeneous 36 := by
  unfold a11224
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00528.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00864.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a11225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11223 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a11224 ^ 1)
theorem ha11225 : a11225.IsHomogeneous 36 := by
  unfold a11225
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha11224.pow 1)))

@[irreducible]
def a11226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a04085 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00528 ^ 1 * a02007 ^ 1)
theorem ha11226 : a11226.IsHomogeneous 36 := by
  unfold a11226
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11226 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11224 ^ 1)
theorem ha11227 : a11227.IsHomogeneous 42 := by
  unfold a11227
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11226.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11224.pow 1)))

@[irreducible]
def a11228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11227 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a11225 ^ 1)
theorem ha11228 : a11228.IsHomogeneous 42 := by
  unfold a11228
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11227.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha11225.pow 1)))

@[irreducible]
def a11229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a03016 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a05883 ^ 1)
theorem ha11229 : a11229.IsHomogeneous 30 := by
  unfold a11229
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha05883.pow 1)))

@[irreducible]
def a11230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11229 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11223 ^ 1)
theorem ha11230 : a11230.IsHomogeneous 36 := by
  unfold a11230
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11229.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11223.pow 1)))

@[irreducible]
def a11231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11230 ^ 1)
theorem ha11231 : a11231.IsHomogeneous 36 := by
  unfold a11231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11230.pow 1)))

@[irreducible]
def a11232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11228 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a11231 ^ 1)
theorem ha11232 : a11232.IsHomogeneous 42 := by
  unfold a11232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha11231.pow 1)))

@[irreducible]
def a11233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a07557 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00161 ^ 1 * a04085 ^ 1)
theorem ha11233 : a11233.IsHomogeneous 30 := by
  unfold a11233
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha07557.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00161.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a11234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11226 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11233 ^ 1)
theorem ha11234 : a11234.IsHomogeneous 36 := by
  unfold a11234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11226.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11233.pow 1)))

@[irreducible]
def a11235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11227 ^ 1)
theorem ha11235 : a11235.IsHomogeneous 42 := by
  unfold a11235
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11227.pow 1)))

@[irreducible]
def a11236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11235 ^ 1)
theorem ha11236 : a11236.IsHomogeneous 42 := by
  unfold a11236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11228.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11235.pow 1)))

@[irreducible]
def a11237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11236 ^ 1)
theorem ha11237 : a11237.IsHomogeneous 42 := by
  unfold a11237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11236.pow 1)))

@[irreducible]
def a11238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10971 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05883 ^ 1)
theorem ha11238 : a11238.IsHomogeneous 30 := by
  unfold a11238
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10971.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05883.pow 1)))

@[irreducible]
def a11239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11238 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11229 ^ 1)
theorem ha11239 : a11239.IsHomogeneous 36 := by
  unfold a11239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11229.pow 1)))

@[irreducible]
def a11240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11239 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11230 ^ 1)
theorem ha11240 : a11240.IsHomogeneous 42 := by
  unfold a11240
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11239.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11230.pow 1)))

@[irreducible]
def a11241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11240 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11231 ^ 1)
theorem ha11241 : a11241.IsHomogeneous 42 := by
  unfold a11241
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11231.pow 1)))

@[irreducible]
def a11242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11232 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a11241 ^ 1)
theorem ha11242 : a11242.IsHomogeneous 42 := by
  unfold a11242
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha11241.pow 1)))

@[irreducible]
def a11243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11242 ^ 1)
theorem ha11243 : a11243.IsHomogeneous 42 := by
  unfold a11243
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11242.pow 1)))

@[irreducible]
def a11244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a01327 ^ 1 * a01473 ^ 1)
theorem ha11244 : a11244.IsHomogeneous 30 := by
  unfold a11244
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha01327.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a11245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a03191 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a01327 ^ 1 * a01473 ^ 1)
theorem ha11245 : a11245.IsHomogeneous 30 := by
  unfold a11245
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha01327.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a11246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11244 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11245 ^ 1)
theorem ha11246 : a11246.IsHomogeneous 30 := by
  unfold a11246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11244.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11245.pow 1)))

@[irreducible]
def a11247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00577 ^ 1 * a02935 ^ 1)
theorem ha11247 : a11247.IsHomogeneous 30 := by
  unfold a11247
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha05754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00577.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11244 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11247 ^ 1)
theorem ha11248 : a11248.IsHomogeneous 30 := by
  unfold a11248
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11244.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11247.pow 1)))

@[irreducible]
def a11249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11246 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11248 ^ 1)
theorem ha11249 : a11249.IsHomogeneous 30 := by
  unfold a11249
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11246.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11248.pow 1)))

@[irreducible]
def a11250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a06158 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a03191 ^ 1)
theorem ha11250 : a11250.IsHomogeneous 30 := by
  unfold a11250
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha06158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a11251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11245 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11250 ^ 1)
theorem ha11251 : a11251.IsHomogeneous 30 := by
  unfold a11251
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11245.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11250.pow 1)))

@[irreducible]
def a11252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11246 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11251 ^ 1)
theorem ha11252 : a11252.IsHomogeneous 30 := by
  unfold a11252
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11246.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11251.pow 1)))

@[irreducible]
def a11253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11252 ^ 1)
theorem ha11253 : a11253.IsHomogeneous 30 := by
  unfold a11253
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11252.pow 1)))

@[irreducible]
def a11254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a10779 ^ 1)
theorem ha11254 : a11254.IsHomogeneous 24 := by
  unfold a11254
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha10779.pow 1)))

@[irreducible]
def a11255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11247 ^ 1)
theorem ha11255 : a11255.IsHomogeneous 30 := by
  unfold a11255
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11254.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11247.pow 1)))

@[irreducible]
def a11256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11248 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11255 ^ 1)
theorem ha11256 : a11256.IsHomogeneous 30 := by
  unfold a11256
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11248.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11255.pow 1)))

@[irreducible]
def a11257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11256 ^ 1)
theorem ha11257 : a11257.IsHomogeneous 30 := by
  unfold a11257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11256.pow 1)))

@[irreducible]
def a11258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11257 ^ 1)
theorem ha11258 : a11258.IsHomogeneous 30 := by
  unfold a11258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11257.pow 1)))

@[irreducible]
def a11259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00506 ^ 1)
theorem ha11259 : a11259.IsHomogeneous 18 := by
  unfold a11259
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00506.pow 1)))

@[irreducible]
def a11260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00506 ^ 1)
theorem ha11260 : a11260.IsHomogeneous 12 := by
  unfold a11260
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a11261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1)
theorem ha11261 : a11261.IsHomogeneous 18 := by
  unfold a11261
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a11262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11259 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11261 ^ 1) + (C ((21 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a11260 ^ 1)
theorem ha11262 : a11262.IsHomogeneous 18 := by
  unfold a11262
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11261.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha11260.pow 1)))

@[irreducible]
def a11263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha11263 : a11263.IsHomogeneous 12 := by
  unfold a11263
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

end CycleQ2Concrete
