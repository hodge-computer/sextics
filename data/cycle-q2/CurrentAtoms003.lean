import Proposal.CurrentAtoms002

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a01536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01535 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01416 ^ 1)
theorem ha01536 : a01536.IsHomogeneous 58 := by
  unfold a01536
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01535.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01416.pow 1)))

@[irreducible]
def a01537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00054 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha01537 : a01537.IsHomogeneous 42 := by
  unfold a01537
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a01538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00201 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00201 ^ 1)
theorem ha01538 : a01538.IsHomogeneous 39 := by
  unfold a01538
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a01539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00054 ^ 1)
theorem ha01539 : a01539.IsHomogeneous 36 := by
  unfold a01539
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)))

@[irreducible]
def a01540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01538 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01539 ^ 1)
theorem ha01540 : a01540.IsHomogeneous 45 := by
  unfold a01540
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01537.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01538.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01539.pow 1)))

@[irreducible]
def a01541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha01541 : a01541.IsHomogeneous 39 := by
  unfold a01541
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a01542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha01542 : a01542.IsHomogeneous 48 := by
  unfold a01542
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha00864.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01542 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01541 ^ 1)
theorem ha01543 : a01543.IsHomogeneous 48 := by
  unfold a01543
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01542.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01541.pow 1)))

@[irreducible]
def a01544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha01544 : a01544.IsHomogeneous 24 := by
  unfold a01544
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a01545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1)
theorem ha01545 : a01545.IsHomogeneous 21 := by
  unfold a01545
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a01546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01544 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01545 ^ 1)
theorem ha01546 : a01546.IsHomogeneous 24 := by
  unfold a01546
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01544.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01545.pow 1)))

@[irreducible]
def a01547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00865 ^ 1)
theorem ha01547 : a01547.IsHomogeneous 27 := by
  unfold a01547
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a01548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01547 ^ 1)
theorem ha01548 : a01548.IsHomogeneous 27 := by
  unfold a01548
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01547.pow 1)))

@[irreducible]
def a01549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01546 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01548 ^ 1)
theorem ha01549 : a01549.IsHomogeneous 27 := by
  unfold a01549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01548.pow 1)))

@[irreducible]
def a01550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00324 ^ 1)
theorem ha01550 : a01550.IsHomogeneous 12 := by
  unfold a01550
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00629 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01550 ^ 1)
theorem ha01551 : a01551.IsHomogeneous 12 := by
  unfold a01551
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01550.pow 1)))

@[irreducible]
def a01552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00324 ^ 1)
theorem ha01552 : a01552.IsHomogeneous 12 := by
  unfold a01552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01550 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01552 ^ 1)
theorem ha01553 : a01553.IsHomogeneous 12 := by
  unfold a01553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01552.pow 1)))

@[irreducible]
def a01554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01551 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01553 ^ 1)
theorem ha01554 : a01554.IsHomogeneous 12 := by
  unfold a01554
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01553.pow 1)))

@[irreducible]
def a01555 : Poly := (C ((-7 : ℂ) / (432 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01554 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01549 ^ 1)
theorem ha01555 : a01555.IsHomogeneous 27 := by
  unfold a01555
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (432 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01549.pow 1)))

@[irreducible]
def a01556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a01555 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00621 ^ 1)
theorem ha01556 : a01556.IsHomogeneous 39 := by
  unfold a01556
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a01557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01538 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a01556 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01541 ^ 1)
theorem ha01557 : a01557.IsHomogeneous 45 := by
  unfold a01557
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01538.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha01556.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01541.pow 1)))

@[irreducible]
def a01558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01557 ^ 1)
theorem ha01558 : a01558.IsHomogeneous 51 := by
  unfold a01558
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01543.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01540.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01557.pow 1)))

@[irreducible]
def a01559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01558 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01393 ^ 1)
theorem ha01559 : a01559.IsHomogeneous 58 := by
  unfold a01559
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01558.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01393.pow 1)))

@[irreducible]
def a01560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01559 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01416 ^ 1)
theorem ha01560 : a01560.IsHomogeneous 58 := by
  unfold a01560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01559.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01416.pow 1)))

@[irreducible]
def a01561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01560 ^ 1)
theorem ha01561 : a01561.IsHomogeneous 58 := by
  unfold a01561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01536.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01560.pow 1)))

@[irreducible]
def a01562 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00324 ^ 1)
theorem ha01562 : a01562.IsHomogeneous 24 := by
  unfold a01562
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00207 ^ 1)
theorem ha01563 : a01563.IsHomogeneous 24 := by
  unfold a01563
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a01564 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00324 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1)
theorem ha01564 : a01564.IsHomogeneous 24 := by
  unfold a01564
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01565 : Poly := (C ((-15 : ℂ) / (28 : ℂ)) * a00003 ^ 6 * a01562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01563 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01564 ^ 1)
theorem ha01565 : a01565.IsHomogeneous 30 := by
  unfold a01565
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (28 : ℂ))).mul (ha00003.pow 6)).mul (ha01562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01563.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01564.pow 1)))

@[irreducible]
def a01566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00632 ^ 1)
theorem ha01566 : a01566.IsHomogeneous 24 := by
  unfold a01566
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a01567 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a00864 ^ 1) + (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00207 ^ 1 * a00316 ^ 1)
theorem ha01567 : a01567.IsHomogeneous 30 := by
  unfold a01567
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01568 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01566 ^ 1) + (C ((-12 : ℂ) / (1 : ℂ)) * a01567 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01562 ^ 1)
theorem ha01568 : a01568.IsHomogeneous 30 := by
  unfold a01568
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01566.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha01567.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01562.pow 1)))

@[irreducible]
def a01569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1)
theorem ha01569 : a01569.IsHomogeneous 6 := by
  unfold a01569
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)))

@[irreducible]
def a01570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00324 ^ 1)
theorem ha01570 : a01570.IsHomogeneous 6 := by
  unfold a01570
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a01571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01569 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01570 ^ 1)
theorem ha01571 : a01571.IsHomogeneous 6 := by
  unfold a01571
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01570.pow 1)))

@[irreducible]
def a01572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00324 ^ 1)
theorem ha01572 : a01572.IsHomogeneous 6 := by
  unfold a01572
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a01573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01570 ^ 1) + (C ((84 : ℂ) / (5 : ℂ)) * a01572 ^ 1)
theorem ha01573 : a01573.IsHomogeneous 6 := by
  unfold a01573
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((84 : ℂ) / (5 : ℂ))).mul (ha01572.pow 1)))

@[irreducible]
def a01574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01571 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01573 ^ 1)
theorem ha01574 : a01574.IsHomogeneous 6 := by
  unfold a01574
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01571.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01573.pow 1)))

@[irreducible]
def a01575 : Poly := (C ((-5 : ℂ) / (168 : ℂ)) * a01574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01469 ^ 1)
theorem ha01575 : a01575.IsHomogeneous 6 := by
  unfold a01575
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (168 : ℂ))).mul (ha01574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01469.pow 1)))

@[irreducible]
def a01576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a01575 ^ 1)
theorem ha01576 : a01576.IsHomogeneous 24 := by
  unfold a01576
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a01577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01576 ^ 1) + (C ((45 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a01566 ^ 1)
theorem ha01577 : a01577.IsHomogeneous 30 := by
  unfold a01577
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01563.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01576.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha01566.pow 1)))

@[irreducible]
def a01578 : Poly := (C ((-15 : ℂ) / (28 : ℂ)) * a00003 ^ 6 * a01568 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01577 ^ 1)
theorem ha01578 : a01578.IsHomogeneous 36 := by
  unfold a01578
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (28 : ℂ))).mul (ha00003.pow 6)).mul (ha01568.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01565.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01577.pow 1)))

@[irreducible]
def a01579 : Poly := (C ((-28 : ℂ) / (135 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01578 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a01432 ^ 1)
theorem ha01579 : a01579.IsHomogeneous 49 := by
  unfold a01579
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-28 : ℂ) / (135 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01578.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01432.pow 1)))

@[irreducible]
def a01580 : Poly := (C ((-56 : ℂ) / (135 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01578 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01579 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a01432 ^ 1)
theorem ha01580 : a01580.IsHomogeneous 49 := by
  unfold a01580
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-56 : ℂ) / (135 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01578.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01579.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01432.pow 1)))

@[irreducible]
def a01581 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a01561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01524 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a01580 ^ 1)
theorem ha01581 : a01581.IsHomogeneous 58 := by
  unfold a01581
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha01561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01524.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha01580.pow 1)))

@[irreducible]
def a01582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00577 ^ 1)
theorem ha01582 : a01582.IsHomogeneous 45 := by
  unfold a01582
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00577.pow 1)))

@[irreducible]
def a01583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a00865 ^ 1)
theorem ha01583 : a01583.IsHomogeneous 39 := by
  unfold a01583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a01584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01582 ^ 1)
theorem ha01584 : a01584.IsHomogeneous 45 := by
  unfold a01584
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01582.pow 1)))

@[irreducible]
def a01585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00577 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a01473 ^ 1)
theorem ha01585 : a01585.IsHomogeneous 48 := by
  unfold a01585
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a01586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01582 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01585 ^ 1)
theorem ha01586 : a01586.IsHomogeneous 48 := by
  unfold a01586
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01585.pow 1)))

@[irreducible]
def a01587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01584 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01586 ^ 1)
theorem ha01587 : a01587.IsHomogeneous 48 := by
  unfold a01587
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01586.pow 1)))

@[irreducible]
def a01588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01439 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01587 ^ 1)
theorem ha01588 : a01588.IsHomogeneous 53 := by
  unfold a01588
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01439.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01587.pow 1)))

@[irreducible]
def a01589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01588 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01587 ^ 1)
theorem ha01589 : a01589.IsHomogeneous 53 := by
  unfold a01589
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01588.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01587.pow 1)))

@[irreducible]
def a01590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00506 ^ 1)
theorem ha01590 : a01590.IsHomogeneous 48 := by
  unfold a01590
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00064 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00506 ^ 1)
theorem ha01591 : a01591.IsHomogeneous 48 := by
  unfold a01591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00064.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01590 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a01591 ^ 1)
theorem ha01592 : a01592.IsHomogeneous 48 := by
  unfold a01592
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha01591.pow 1)))

@[irreducible]
def a01593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01593 : a01593.IsHomogeneous 30 := by
  unfold a01593
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1)
theorem ha01594 : a01594.IsHomogeneous 30 := by
  unfold a01594
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1)
theorem ha01595 : a01595.IsHomogeneous 27 := by
  unfold a01595
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01593 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01594 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01595 ^ 1)
theorem ha01596 : a01596.IsHomogeneous 30 := by
  unfold a01596
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01593.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01594.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01595.pow 1)))

@[irreducible]
def a01597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00129 ^ 1)
theorem ha01597 : a01597.IsHomogeneous 33 := by
  unfold a01597
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00129 ^ 1)
theorem ha01598 : a01598.IsHomogeneous 30 := by
  unfold a01598
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01597 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01593 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a01598 ^ 1)
theorem ha01599 : a01599.IsHomogeneous 33 := by
  unfold a01599
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01593.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha01598.pow 1)))

@[irreducible]
def a01600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00317 ^ 1)
theorem ha01600 : a01600.IsHomogeneous 33 := by
  unfold a01600
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01597 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01595 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01600 ^ 1)
theorem ha01601 : a01601.IsHomogeneous 33 := by
  unfold a01601
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01595.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01600.pow 1)))

@[irreducible]
def a01602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01599 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01601 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01596 ^ 1)
theorem ha01602 : a01602.IsHomogeneous 33 := by
  unfold a01602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01599.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01601.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01596.pow 1)))

@[irreducible]
def a01603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1)
theorem ha01603 : a01603.IsHomogeneous 6 := by
  unfold a01603
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)))

@[irreducible]
def a01604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00649 ^ 1)
theorem ha01604 : a01604.IsHomogeneous 12 := by
  unfold a01604
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a01605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a01603 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01604 ^ 1)
theorem ha01605 : a01605.IsHomogeneous 12 := by
  unfold a01605
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha01603.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01604.pow 1)))

@[irreducible]
def a01606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha01606 : a01606.IsHomogeneous 12 := by
  unfold a01606
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a01607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01606 ^ 1)
theorem ha01607 : a01607.IsHomogeneous 12 := by
  unfold a01607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01606.pow 1)))

@[irreducible]
def a01608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01607 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00649 ^ 1)
theorem ha01608 : a01608.IsHomogeneous 18 := by
  unfold a01608
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00649.pow 1)))

@[irreducible]
def a01609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01608 ^ 1) + (C ((5 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a01604 ^ 1)
theorem ha01609 : a01609.IsHomogeneous 18 := by
  unfold a01609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01608.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha01604.pow 1)))

@[irreducible]
def a01610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01609 ^ 1) + (C ((5 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a01605 ^ 1)
theorem ha01610 : a01610.IsHomogeneous 18 := by
  unfold a01610
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01609.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha01605.pow 1)))

@[irreducible]
def a01611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00574 ^ 1)
theorem ha01611 : a01611.IsHomogeneous 18 := by
  unfold a01611
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a01612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00324 ^ 1)
theorem ha01612 : a01612.IsHomogeneous 12 := by
  unfold a01612
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01611 ^ 1)
theorem ha01613 : a01613.IsHomogeneous 18 := by
  unfold a01613
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01612.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01611.pow 1)))

@[irreducible]
def a01614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00574 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01469 ^ 1)
theorem ha01614 : a01614.IsHomogeneous 18 := by
  unfold a01614
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00574.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a01615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01611 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01614 ^ 1)
theorem ha01615 : a01615.IsHomogeneous 18 := by
  unfold a01615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01611.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01614.pow 1)))

@[irreducible]
def a01616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01615 ^ 1)
theorem ha01616 : a01616.IsHomogeneous 18 := by
  unfold a01616
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01615.pow 1)))

@[irreducible]
def a01617 : Poly := (C ((-7 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01602 ^ 1) + (C ((7 : ℂ) / (540 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01616 ^ 1)
theorem ha01617 : a01617.IsHomogeneous 33 := by
  unfold a01617
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01602.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (540 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01616.pow 1)))

@[irreducible]
def a01618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00655 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01617 ^ 1)
theorem ha01618 : a01618.IsHomogeneous 39 := by
  unfold a01618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a01619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01590 ^ 1)
theorem ha01619 : a01619.IsHomogeneous 48 := by
  unfold a01619
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01590.pow 1)))

@[irreducible]
def a01620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01592 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01619 ^ 1)
theorem ha01620 : a01620.IsHomogeneous 48 := by
  unfold a01620
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01592.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01619.pow 1)))

@[irreducible]
def a01621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01439 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01620 ^ 1)
theorem ha01621 : a01621.IsHomogeneous 53 := by
  unfold a01621
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01439.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01620.pow 1)))

@[irreducible]
def a01622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01621 ^ 1)
theorem ha01622 : a01622.IsHomogeneous 53 := by
  unfold a01622
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01588.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01621.pow 1)))

@[irreducible]
def a01623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01622 ^ 1)
theorem ha01623 : a01623.IsHomogeneous 53 := by
  unfold a01623
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01622.pow 1)))

@[irreducible]
def a01624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01589 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01587 ^ 1)
theorem ha01624 : a01624.IsHomogeneous 53 := by
  unfold a01624
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01589.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01587.pow 1)))

@[irreducible]
def a01625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01624 ^ 1)
theorem ha01625 : a01625.IsHomogeneous 53 := by
  unfold a01625
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01624.pow 1)))

@[irreducible]
def a01626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00168 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00042 ^ 1 * a00168 ^ 1)
theorem ha01626 : a01626.IsHomogeneous 48 := by
  unfold a01626
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a01627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha01627 : a01627.IsHomogeneous 39 := by
  unfold a01627
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha01628 : a01628.IsHomogeneous 36 := by
  unfold a01628
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01626 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01628 ^ 1)
theorem ha01629 : a01629.IsHomogeneous 48 := by
  unfold a01629
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01626.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01628.pow 1)))

@[irreducible]
def a01630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00168 ^ 1)
theorem ha01630 : a01630.IsHomogeneous 45 := by
  unfold a01630
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a01631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00042 ^ 1 * a01412 ^ 1)
theorem ha01631 : a01631.IsHomogeneous 48 := by
  unfold a01631
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a01632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01630 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a01631 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01626 ^ 1)
theorem ha01632 : a01632.IsHomogeneous 48 := by
  unfold a01632
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01630.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha01631.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01626.pow 1)))

@[irreducible]
def a01633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00317 ^ 1)
theorem ha01633 : a01633.IsHomogeneous 39 := by
  unfold a01633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01627 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a01633 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01630 ^ 1)
theorem ha01634 : a01634.IsHomogeneous 45 := by
  unfold a01634
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01627.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha01633.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01630.pow 1)))

@[irreducible]
def a01635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01629 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01632 ^ 1)
theorem ha01635 : a01635.IsHomogeneous 48 := by
  unfold a01635
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01629.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01632.pow 1)))

@[irreducible]
def a01636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01359 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01635 ^ 1)
theorem ha01636 : a01636.IsHomogeneous 53 := by
  unfold a01636
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01359.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01635.pow 1)))

@[irreducible]
def a01637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01636 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01635 ^ 1)
theorem ha01637 : a01637.IsHomogeneous 53 := by
  unfold a01637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01636.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01635.pow 1)))

@[irreducible]
def a01638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00054 ^ 1 * a00155 ^ 1)
theorem ha01638 : a01638.IsHomogeneous 48 := by
  unfold a01638
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a01639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00201 ^ 1)
theorem ha01639 : a01639.IsHomogeneous 39 := by
  unfold a01639
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a01640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha01640 : a01640.IsHomogeneous 36 := by
  unfold a01640
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a01641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01639 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01638 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01640 ^ 1)
theorem ha01641 : a01641.IsHomogeneous 48 := by
  unfold a01641
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01638.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01640.pow 1)))

@[irreducible]
def a01642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a00506 ^ 1)
theorem ha01642 : a01642.IsHomogeneous 45 := by
  unfold a01642
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00054 ^ 1 * a01327 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha01643 : a01643.IsHomogeneous 48 := by
  unfold a01643
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01642 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01638 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01643 ^ 1)
theorem ha01644 : a01644.IsHomogeneous 48 := by
  unfold a01644
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01638.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01643.pow 1)))

@[irreducible]
def a01645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a01555 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1)
theorem ha01645 : a01645.IsHomogeneous 39 := by
  unfold a01645
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a01646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01639 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a01645 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01642 ^ 1)
theorem ha01646 : a01646.IsHomogeneous 45 := by
  unfold a01646
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01639.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha01645.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01642.pow 1)))

@[irreducible]
def a01647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01646 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01641 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01644 ^ 1)
theorem ha01647 : a01647.IsHomogeneous 48 := by
  unfold a01647
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01641.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01644.pow 1)))

@[irreducible]
def a01648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01359 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01647 ^ 1)
theorem ha01648 : a01648.IsHomogeneous 53 := by
  unfold a01648
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01359.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01647.pow 1)))

@[irreducible]
def a01649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01636 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01648 ^ 1)
theorem ha01649 : a01649.IsHomogeneous 53 := by
  unfold a01649
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01636.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01648.pow 1)))

@[irreducible]
def a01650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01649 ^ 1)
theorem ha01650 : a01650.IsHomogeneous 53 := by
  unfold a01650
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01637.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01649.pow 1)))

@[irreducible]
def a01651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01648 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01647 ^ 1)
theorem ha01651 : a01651.IsHomogeneous 53 := by
  unfold a01651
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01648.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01647.pow 1)))

@[irreducible]
def a01652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01651 ^ 1)
theorem ha01652 : a01652.IsHomogeneous 53 := by
  unfold a01652
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01651.pow 1)))

@[irreducible]
def a01653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01650 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01652 ^ 1)
theorem ha01653 : a01653.IsHomogeneous 53 := by
  unfold a01653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01650.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01652.pow 1)))

@[irreducible]
def a01654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00171 ^ 1 * a00324 ^ 1)
theorem ha01654 : a01654.IsHomogeneous 48 := by
  unfold a01654
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00317 ^ 1)
theorem ha01655 : a01655.IsHomogeneous 39 := by
  unfold a01655
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1)
theorem ha01656 : a01656.IsHomogeneous 42 := by
  unfold a01656
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a01657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01656 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a01654 ^ 1)
theorem ha01657 : a01657.IsHomogeneous 48 := by
  unfold a01657
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01656.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha01654.pow 1)))

@[irreducible]
def a01658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00129 ^ 1 * a00555 ^ 1)
theorem ha01658 : a01658.IsHomogeneous 45 := by
  unfold a01658
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a01659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1 * a00555 ^ 1)
theorem ha01659 : a01659.IsHomogeneous 42 := by
  unfold a01659
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a01660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01658 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a01659 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01654 ^ 1)
theorem ha01660 : a01660.IsHomogeneous 48 := by
  unfold a01660
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01658.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha01659.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01654.pow 1)))

@[irreducible]
def a01661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00317 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00317 ^ 1)
theorem ha01661 : a01661.IsHomogeneous 39 := by
  unfold a01661
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01655 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a01658 ^ 1) + (C ((10 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a01661 ^ 1)
theorem ha01662 : a01662.IsHomogeneous 45 := by
  unfold a01662
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha01658.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha01661.pow 1)))

@[irreducible]
def a01663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01657 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a01660 ^ 1)
theorem ha01663 : a01663.IsHomogeneous 48 := by
  unfold a01663
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01657.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha01660.pow 1)))

@[irreducible]
def a01664 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00155 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00506 ^ 1)
theorem ha01664 : a01664.IsHomogeneous 30 := by
  unfold a01664
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1)
theorem ha01665 : a01665.IsHomogeneous 24 := by
  unfold a01665
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01666 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00058 ^ 1)
theorem ha01666 : a01666.IsHomogeneous 24 := by
  unfold a01666
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a01667 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a01666 ^ 1) + (C ((-7 : ℂ) / (8 : ℂ)) * a01664 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01665 ^ 1)
theorem ha01667 : a01667.IsHomogeneous 30 := by
  unfold a01667
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha01666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha01664.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01665.pow 1)))

@[irreducible]
def a01668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a00506 ^ 1)
theorem ha01668 : a01668.IsHomogeneous 30 := by
  unfold a01668
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01669 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00506 ^ 1) + (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00058 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a00506 ^ 1)
theorem ha01669 : a01669.IsHomogeneous 30 := by
  unfold a01669
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01670 : Poly := (C ((-48 : ℂ) / (7 : ℂ)) * a01669 ^ 1) + (C ((-4 : ℂ) / (1 : ℂ)) * a01668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01664 ^ 1)
theorem ha01670 : a01670.IsHomogeneous 30 := by
  unfold a01670
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (7 : ℂ))).mul (ha01669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01668.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01664.pow 1)))

@[irreducible]
def a01671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a01575 ^ 1)
theorem ha01671 : a01671.IsHomogeneous 24 := by
  unfold a01671
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a01672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01665 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01671 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a01668 ^ 1)
theorem ha01672 : a01672.IsHomogeneous 30 := by
  unfold a01672
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01665.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01671.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha01668.pow 1)))

@[irreducible]
def a01673 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a01670 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01672 ^ 1)
theorem ha01673 : a01673.IsHomogeneous 30 := by
  unfold a01673
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha01670.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01667.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01672.pow 1)))

@[irreducible]
def a01674 : Poly := (C ((-1 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01663 ^ 1)
theorem ha01674 : a01674.IsHomogeneous 48 := by
  unfold a01674
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01663.pow 1)))

@[irreducible]
def a01675 : Poly := (C ((-1 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01663 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01674 ^ 1)
theorem ha01675 : a01675.IsHomogeneous 48 := by
  unfold a01675
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01674.pow 1)))

@[irreducible]
def a01676 : Poly := (C ((-2 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01674 ^ 1)
theorem ha01676 : a01676.IsHomogeneous 48 := by
  unfold a01676
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01674.pow 1)))

@[irreducible]
def a01677 : Poly := (C ((-1 : ℂ) / (567 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01675 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01676 ^ 1)
theorem ha01677 : a01677.IsHomogeneous 48 := by
  unfold a01677
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (567 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01675.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01676.pow 1)))

@[irreducible]
def a01678 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a01653 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01625 ^ 1) + (C ((28 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01677 ^ 1)
theorem ha01678 : a01678.IsHomogeneous 53 := by
  unfold a01678
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha01653.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01625.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01677.pow 1)))

@[irreducible]
def a01679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00655 ^ 1)
theorem ha01679 : a01679.IsHomogeneous 42 := by
  unfold a01679
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a01680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00218 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00064 ^ 1 * a00864 ^ 1)
theorem ha01680 : a01680.IsHomogeneous 48 := by
  unfold a01680
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00218.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00064.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a01681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01679 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01680 ^ 1)
theorem ha01681 : a01681.IsHomogeneous 48 := by
  unfold a01681
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01680.pow 1)))

@[irreducible]
def a01682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01617 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00655 ^ 1)
theorem ha01682 : a01682.IsHomogeneous 39 := by
  unfold a01682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00655.pow 1)))

@[irreducible]
def a01683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01682 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01679 ^ 1)
theorem ha01683 : a01683.IsHomogeneous 45 := by
  unfold a01683
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01682.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01679.pow 1)))

@[irreducible]
def a01684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01683 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01681 ^ 1)
theorem ha01684 : a01684.IsHomogeneous 51 := by
  unfold a01684
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01683.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01681.pow 1)))

@[irreducible]
def a01685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01519 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a01684 ^ 1)
theorem ha01685 : a01685.IsHomogeneous 51 := by
  unfold a01685
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha01684.pow 1)))

@[irreducible]
def a01686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01685 ^ 1)
theorem ha01686 : a01686.IsHomogeneous 51 := by
  unfold a01686
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01685.pow 1)))

@[irreducible]
def a01687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01686 ^ 1)
theorem ha01687 : a01687.IsHomogeneous 51 := by
  unfold a01687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01686.pow 1)))

@[irreducible]
def a01688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01684 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a01685 ^ 1)
theorem ha01688 : a01688.IsHomogeneous 51 := by
  unfold a01688
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01684.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha01685.pow 1)))

@[irreducible]
def a01689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01686 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a01688 ^ 1)
theorem ha01689 : a01689.IsHomogeneous 51 := by
  unfold a01689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01686.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha01688.pow 1)))

@[irreducible]
def a01690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01689 ^ 1)
theorem ha01690 : a01690.IsHomogeneous 51 := by
  unfold a01690
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01689.pow 1)))

@[irreducible]
def a01691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01687 ^ 1)
theorem ha01691 : a01691.IsHomogeneous 51 := by
  unfold a01691
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01687.pow 1)))

@[irreducible]
def a01692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01691 ^ 1)
theorem ha01692 : a01692.IsHomogeneous 51 := by
  unfold a01692
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01690.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01691.pow 1)))

@[irreducible]
def a01693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01558 ^ 1)
theorem ha01693 : a01693.IsHomogeneous 51 := by
  unfold a01693
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01558.pow 1)))

@[irreducible]
def a01694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01693 ^ 1)
theorem ha01694 : a01694.IsHomogeneous 51 := by
  unfold a01694
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01693.pow 1)))

@[irreducible]
def a01695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01694 ^ 1)
theorem ha01695 : a01695.IsHomogeneous 51 := by
  unfold a01695
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01694.pow 1)))

@[irreducible]
def a01696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01693 ^ 1)
theorem ha01696 : a01696.IsHomogeneous 51 := by
  unfold a01696
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01693.pow 1)))

@[irreducible]
def a01697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01696 ^ 1)
theorem ha01697 : a01697.IsHomogeneous 51 := by
  unfold a01697
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01696.pow 1)))

@[irreducible]
def a01698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01695 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01697 ^ 1)
theorem ha01698 : a01698.IsHomogeneous 51 := by
  unfold a01698
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01697.pow 1)))

@[irreducible]
def a01699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01696 ^ 1)
theorem ha01699 : a01699.IsHomogeneous 51 := by
  unfold a01699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01696.pow 1)))

@[irreducible]
def a01700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01699 ^ 1)
theorem ha01700 : a01700.IsHomogeneous 51 := by
  unfold a01700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01699.pow 1)))

@[irreducible]
def a01701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01698 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01700 ^ 1)
theorem ha01701 : a01701.IsHomogeneous 51 := by
  unfold a01701
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01698.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01700.pow 1)))

@[irreducible]
def a01702 : Poly := (C ((-28 : ℂ) / (729 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01578 ^ 1) + (C ((-2 : ℂ) / (3 : ℂ)) * a01701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01692 ^ 1)
theorem ha01702 : a01702.IsHomogeneous 51 := by
  unfold a01702
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-28 : ℂ) / (729 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01578.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha01701.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01692.pow 1)))

@[irreducible]
def a01703 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00012 ^ 5 * a00014 ^ 3 * a01360 ^ 1) + (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a00014 ^ 1 * a01507 ^ 1) + (C ((-1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a01581 ^ 1) + (C ((-1 : ℂ) / (7680 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 6 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 2 * a01433 ^ 1) + (C ((1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a01678 ^ 1)
theorem ha01703 : a01703.IsHomogeneous 89 := by
  unfold a01703
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 5)).mul (ha00014.pow 3)).mul (ha01360.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha00014.pow 1)).mul (ha01507.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha01581.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (7680 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha01702.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha01433.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a01704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a01703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00713 ^ 1)
theorem ha01704 : a01704.IsHomogeneous 175 := by
  unfold a01704
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha01703.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00713.pow 1)))

@[irreducible]
def a01705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00713 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01704 ^ 1)
theorem ha01705 : a01705.IsHomogeneous 175 := by
  unfold a01705
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01704.pow 1)))

@[irreducible]
def a01706 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00714 ^ 1)
theorem ha01706 : a01706.IsHomogeneous 255 := by
  unfold a01706
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00714.pow 1)))

@[irreducible]
def a01707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01706 ^ 1)
theorem ha01707 : a01707.IsHomogeneous 255 := by
  unfold a01707
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01706.pow 1)))

@[irreducible]
def a01708 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00295 ^ 1 * a00715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01707 ^ 1)
theorem ha01708 : a01708.IsHomogeneous 638 := by
  unfold a01708
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00295.pow 1)).mul (ha00715.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a01709 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a01319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01708 ^ 1)
theorem ha01709 : a01709.IsHomogeneous 892 := by
  unfold a01709
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha01319.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01708.pow 1)))

@[irreducible]
def a01710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00294 ^ 1 * a00795 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a00800 ^ 1)
theorem ha01710 : a01710.IsHomogeneous 655 := by
  unfold a01710
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00294.pow 1)).mul (ha00795.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha00800.pow 1)))

@[irreducible]
def a01711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00291 ^ 1 * a00778 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00287 ^ 1 * a00793 ^ 1)
theorem ha01711 : a01711.IsHomogeneous 702 := by
  unfold a01711
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha00778.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00287.pow 1)).mul (ha00793.pow 1)))

@[irreducible]
def a01712 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a00734 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00271 ^ 1 * a00776 ^ 1)
theorem ha01712 : a01712.IsHomogeneous 424 := by
  unfold a01712
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha00734.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00271.pow 1)).mul (ha00776.pow 1)))

@[irreducible]
def a01713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00270 ^ 1 * a00724 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a00265 ^ 1 * a00732 ^ 1)
theorem ha01713 : a01713.IsHomogeneous 134 := by
  unfold a01713
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00270.pow 1)).mul (ha00724.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00732.pow 1)))

@[irreducible]
def a01714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a00723 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00785 ^ 1)
theorem ha01714 : a01714.IsHomogeneous 110 := by
  unfold a01714
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha00723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00785.pow 1)))

@[irreducible]
def a01715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00262 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00717 ^ 1)
theorem ha01715 : a01715.IsHomogeneous 46 := by
  unfold a01715
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a01716 : Poly := (C ((-7 : ℂ) / (87480 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00004 ^ 6 * a00005 ^ 3 * a00862 ^ 1) + (C ((-1 : ℂ) / (1080 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00102 ^ 1 * a00864 ^ 1)
theorem ha01716 : a01716.IsHomogeneous 39 := by
  unfold a01716
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (87480 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00862.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1080 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00102.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a01717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1)
theorem ha01717 : a01717.IsHomogeneous 46 := by
  unfold a01717
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a01718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01715 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a01717 ^ 1)
theorem ha01718 : a01718.IsHomogeneous 46 := by
  unfold a01718
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01715.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha01717.pow 1)))

@[irreducible]
def a01719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00756 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a01715 ^ 1)
theorem ha01719 : a01719.IsHomogeneous 46 := by
  unfold a01719
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha01715.pow 1)))

@[irreducible]
def a01720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01718 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a01719 ^ 1)
theorem ha01720 : a01720.IsHomogeneous 46 := by
  unfold a01720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha01719.pow 1)))

@[irreducible]
def a01721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a01335 ^ 1) + (C ((7 : ℂ) / (90 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1)
theorem ha01721 : a01721.IsHomogeneous 19 := by
  unfold a01721
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha01335.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (90 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a01722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00104 ^ 1 * a01721 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00264 ^ 1 * a00721 ^ 1)
theorem ha01722 : a01722.IsHomogeneous 49 := by
  unfold a01722
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00104.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00264.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a01723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a00721 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a01722 ^ 1)
theorem ha01723 : a01723.IsHomogeneous 49 := by
  unfold a01723
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha00721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha01722.pow 1)))

@[irreducible]
def a01724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a01723 ^ 1) + (C ((21 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a01720 ^ 1)
theorem ha01724 : a01724.IsHomogeneous 53 := by
  unfold a01724
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha01723.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha01720.pow 1)))

@[irreducible]
def a01725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a00723 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a01724 ^ 1)
theorem ha01725 : a01725.IsHomogeneous 109 := by
  unfold a01725
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha00723.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha01724.pow 1)))

@[irreducible]
def a01726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a01725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a01714 ^ 1)
theorem ha01726 : a01726.IsHomogeneous 165 := by
  unfold a01726
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha01725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha01714.pow 1)))

@[irreducible]
def a01727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00270 ^ 1 * a00724 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00117 ^ 1 * a01726 ^ 1)
theorem ha01727 : a01727.IsHomogeneous 189 := by
  unfold a01727
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00270.pow 1)).mul (ha00724.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00117.pow 1)).mul (ha01726.pow 1)))

@[irreducible]
def a01728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01727 ^ 1)
theorem ha01728 : a01728.IsHomogeneous 189 := by
  unfold a01728
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01727.pow 1)))

@[irreducible]
def a01729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00108 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00726 ^ 1)
theorem ha01729 : a01729.IsHomogeneous 22 := by
  unfold a01729
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00108.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00726.pow 1)))

@[irreducible]
def a01730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00726 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01729 ^ 1)
theorem ha01730 : a01730.IsHomogeneous 22 := by
  unfold a01730
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01729.pow 1)))

@[irreducible]
def a01731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00726 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01730 ^ 1)
theorem ha01731 : a01731.IsHomogeneous 22 := by
  unfold a01731
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01730.pow 1)))

@[irreducible]
def a01732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2) + (C ((1 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3)
theorem ha01732 : a01732.IsHomogeneous 15 := by
  unfold a01732
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a01733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00005 ^ 1 * a01732 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00729 ^ 1)
theorem ha01733 : a01733.IsHomogeneous 20 := by
  unfold a01733
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00005.pow 1)).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00729.pow 1)))

@[irreducible]
def a01734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00729 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01733 ^ 1)
theorem ha01734 : a01734.IsHomogeneous 20 := by
  unfold a01734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01733.pow 1)))

@[irreducible]
def a01735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00729 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01734 ^ 1)
theorem ha01735 : a01735.IsHomogeneous 20 := by
  unfold a01735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01734.pow 1)))

@[irreducible]
def a01736 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a01735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01731 ^ 1)
theorem ha01736 : a01736.IsHomogeneous 22 := by
  unfold a01736
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha01735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01731.pow 1)))

@[irreducible]
def a01737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a00732 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00105 ^ 1 * a01736 ^ 1)
theorem ha01737 : a01737.IsHomogeneous 77 := by
  unfold a01737
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha00732.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00105.pow 1)).mul (ha01736.pow 1)))

@[irreducible]
def a01738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01713 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a01737 ^ 1)
theorem ha01738 : a01738.IsHomogeneous 134 := by
  unfold a01738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01713.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha01737.pow 1)))

@[irreducible]
def a01739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01728 ^ 1)
theorem ha01739 : a01739.IsHomogeneous 189 := by
  unfold a01739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01728.pow 1)))

@[irreducible]
def a01740 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00286 ^ 1 * a00734 ^ 1)
theorem ha01740 : a01740.IsHomogeneous 334 := by
  unfold a01740
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01739.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00286.pow 1)).mul (ha00734.pow 1)))

@[irreducible]
def a01741 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01740 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01712 ^ 1)
theorem ha01741 : a01741.IsHomogeneous 479 := by
  unfold a01741
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01740.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01712.pow 1)))

@[irreducible]
def a01742 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 2)
theorem ha01742 : a01742.IsHomogeneous 290 := by
  unfold a01742
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 2)))

@[irreducible]
def a01743 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01742 ^ 1)
theorem ha01743 : a01743.IsHomogeneous 290 := by
  unfold a01743
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01742.pow 1)))

@[irreducible]
def a01744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00123 ^ 1 * a00262 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00103 ^ 1 * a00285 ^ 1)
theorem ha01744 : a01744.IsHomogeneous 139 := by
  unfold a01744
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00123.pow 1)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1)))

@[irreducible]
def a01745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a00262 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00123 ^ 1 * a00737 ^ 1)
theorem ha01745 : a01745.IsHomogeneous 179 := by
  unfold a01745
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a01746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00285 ^ 1)
theorem ha01746 : a01746.IsHomogeneous 139 := by
  unfold a01746
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00773.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00285.pow 1)))

@[irreducible]
def a01747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01744 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01745 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00103 ^ 1 * a01746 ^ 1)
theorem ha01747 : a01747.IsHomogeneous 181 := by
  unfold a01747
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01744.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01745.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00103.pow 1)).mul (ha01746.pow 1)))

@[irreducible]
def a01748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a00737 ^ 1)
theorem ha01748 : a01748.IsHomogeneous 185 := by
  unfold a01748
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a01749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a01716 ^ 1)
theorem ha01749 : a01749.IsHomogeneous 81 := by
  unfold a01749
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a01750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a00717 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01749 ^ 1)
theorem ha01750 : a01750.IsHomogeneous 81 := by
  unfold a01750
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha00717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01749.pow 1)))

@[irreducible]
def a01751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a01750 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00123 ^ 1 * a00737 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a00737 ^ 1)
theorem ha01751 : a01751.IsHomogeneous 185 := by
  unfold a01751
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha01750.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00123.pow 1)).mul (ha00737.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a01752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01745 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01748 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01751 ^ 1)
theorem ha01752 : a01752.IsHomogeneous 185 := by
  unfold a01752
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01745.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01748.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01751.pow 1)))

@[irreducible]
def a01753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00276 ^ 1 * a00749 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00275 ^ 1 * a00751 ^ 1)
theorem ha01753 : a01753.IsHomogeneous 90 := by
  unfold a01753
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00276.pow 1)).mul (ha00749.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00275.pow 1)).mul (ha00751.pow 1)))

@[irreducible]
def a01754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1)
theorem ha01754 : a01754.IsHomogeneous 48 := by
  unfold a01754
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00262 ^ 1)
theorem ha01755 : a01755.IsHomogeneous 46 := by
  unfold a01755
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1)
theorem ha01756 : a01756.IsHomogeneous 48 := by
  unfold a01756
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01756 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a01755 ^ 1)
theorem ha01757 : a01757.IsHomogeneous 48 := by
  unfold a01757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01754.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01756.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha01755.pow 1)))

@[irreducible]
def a01758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00262 ^ 1)
theorem ha01758 : a01758.IsHomogeneous 52 := by
  unfold a01758
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00717 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00717 ^ 1)
theorem ha01759 : a01759.IsHomogeneous 52 := by
  unfold a01759
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a01760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01755 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01759 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a01758 ^ 1)
theorem ha01760 : a01760.IsHomogeneous 52 := by
  unfold a01760
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01755.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01759.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha01758.pow 1)))

@[irreducible]
def a01761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00009 ^ 1 * a00262 ^ 1)
theorem ha01761 : a01761.IsHomogeneous 48 := by
  unfold a01761
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a01756 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a01761 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a01758 ^ 1)
theorem ha01762 : a01762.IsHomogeneous 52 := by
  unfold a01762
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha01756.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha01761.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha01758.pow 1)))

@[irreducible]
def a01763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a01757 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01762 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01760 ^ 1)
theorem ha01763 : a01763.IsHomogeneous 52 := by
  unfold a01763
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha01757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01762.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01760.pow 1)))

@[irreducible]
def a01764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00104 ^ 1)
theorem ha01764 : a01764.IsHomogeneous 25 := by
  unfold a01764
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00104.pow 1)))

@[irreducible]
def a01765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00722 ^ 1)
theorem ha01765 : a01765.IsHomogeneous 50 := by
  unfold a01765
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00722.pow 1)))

@[irreducible]
def a01766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a01764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01765 ^ 1)
theorem ha01766 : a01766.IsHomogeneous 50 := by
  unfold a01766
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha01764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01765.pow 1)))

@[irreducible]
def a01767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00722 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01723 ^ 1)
theorem ha01767 : a01767.IsHomogeneous 55 := by
  unfold a01767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01723.pow 1)))

@[irreducible]
def a01768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01765 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a01767 ^ 1)
theorem ha01768 : a01768.IsHomogeneous 55 := by
  unfold a01768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha01767.pow 1)))

@[irreducible]
def a01769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01766 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01768 ^ 1)
theorem ha01769 : a01769.IsHomogeneous 55 := by
  unfold a01769
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01768.pow 1)))

@[irreducible]
def a01770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00130 ^ 1 * a00721 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a00574 ^ 1)
theorem ha01770 : a01770.IsHomogeneous 37 := by
  unfold a01770
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a01771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00721 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 5 * a00025 ^ 1 * a01721 ^ 1)
theorem ha01771 : a01771.IsHomogeneous 30 := by
  unfold a01771
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00721.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 5)).mul (ha00025.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a01772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01770 ^ 1)
theorem ha01772 : a01772.IsHomogeneous 37 := by
  unfold a01772
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01770.pow 1)))

@[irreducible]
def a01773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00104 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00264 ^ 1 * a00574 ^ 1)
theorem ha01773 : a01773.IsHomogeneous 37 := by
  unfold a01773
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00264.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a01774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01770 ^ 1) + (C ((14 : ℂ) / (1 : ℂ)) * a01773 ^ 1)
theorem ha01774 : a01774.IsHomogeneous 37 := by
  unfold a01774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (1 : ℂ))).mul (ha01773.pow 1)))

@[irreducible]
def a01775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01772 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01774 ^ 1)
theorem ha01775 : a01775.IsHomogeneous 37 := by
  unfold a01775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01772.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01774.pow 1)))

@[irreducible]
def a01776 : Poly := (C ((-1 : ℂ) / (720 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a01775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a01769 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a01763 ^ 1)
theorem ha01776 : a01776.IsHomogeneous 59 := by
  unfold a01776
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (720 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha01775.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha01769.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha01763.pow 1)))

@[irreducible]
def a01777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00276 ^ 1 * a00749 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00120 ^ 1 * a01776 ^ 1)
theorem ha01777 : a01777.IsHomogeneous 90 := by
  unfold a01777
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00276.pow 1)).mul (ha00749.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00120.pow 1)).mul (ha01776.pow 1)))

@[irreducible]
def a01778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01753 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01777 ^ 1)
theorem ha01778 : a01778.IsHomogeneous 90 := by
  unfold a01778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01777.pow 1)))

@[irreducible]
def a01779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00119 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 5 * a00012 ^ 2 * a01327 ^ 1) + (C ((7 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00004 ^ 4 * a00005 ^ 1 * a00862 ^ 1)
theorem ha01779 : a01779.IsHomogeneous 28 := by
  unfold a01779
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00119.pow 1)).mul (ha00864.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 5)).mul (ha00012.pow 2)).mul (ha01327.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00862.pow 1)))

@[irreducible]
def a01780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00118 ^ 1 * a01779 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00275 ^ 1 * a00751 ^ 1)
theorem ha01780 : a01780.IsHomogeneous 90 := by
  unfold a01780
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00118.pow 1)).mul (ha01779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00275.pow 1)).mul (ha00751.pow 1)))

@[irreducible]
def a01781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01753 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a01780 ^ 1)
theorem ha01781 : a01781.IsHomogeneous 90 := by
  unfold a01781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha01780.pow 1)))

@[irreducible]
def a01782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01778 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01781 ^ 1)
theorem ha01782 : a01782.IsHomogeneous 90 := by
  unfold a01782
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01778.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01781.pow 1)))

@[irreducible]
def a01783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1 * a00280 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a00717 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00121 ^ 1 * a00262 ^ 1)
theorem ha01783 : a01783.IsHomogeneous 94 := by
  unfold a01783
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00280.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00121.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1 * a00280 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a00762 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00280 ^ 1)
theorem ha01784 : a01784.IsHomogeneous 94 := by
  unfold a01784
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00280.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a01785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00121 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00103 ^ 1 * a00280 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00121 ^ 1 * a00262 ^ 1)
theorem ha01785 : a01785.IsHomogeneous 90 := by
  unfold a01785
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00121.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00103.pow 1)).mul (ha00280.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00121.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a01786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a01785 ^ 1) + (C ((324 : ℂ) / (35 : ℂ)) * a01783 ^ 1) + (C ((324 : ℂ) / (35 : ℂ)) * a01784 ^ 1)
theorem ha01786 : a01786.IsHomogeneous 94 := by
  unfold a01786
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha01785.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((324 : ℂ) / (35 : ℂ))).mul (ha01783.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((324 : ℂ) / (35 : ℂ))).mul (ha01784.pow 1)))

@[irreducible]
def a01787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1 * a00762 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00280 ^ 1 * a00717 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a00280 ^ 1)
theorem ha01787 : a01787.IsHomogeneous 92 := by
  unfold a01787
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a01788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00121 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a00717 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00280 ^ 1 * a00717 ^ 1)
theorem ha01788 : a01788.IsHomogeneous 94 := by
  unfold a01788
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a01789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01787 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01788 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a01783 ^ 1)
theorem ha01789 : a01789.IsHomogeneous 94 := by
  unfold a01789
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01787.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01788.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha01783.pow 1)))

@[irreducible]
def a01790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha01790 : a01790.IsHomogeneous 42 := by
  unfold a01790
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a01791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1)
theorem ha01791 : a01791.IsHomogeneous 40 := by
  unfold a01791
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a01792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01790 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a01791 ^ 1)
theorem ha01792 : a01792.IsHomogeneous 42 := by
  unfold a01792
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01790.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha01791.pow 1)))

@[irreducible]
def a01793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00717 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a01716 ^ 1)
theorem ha01793 : a01793.IsHomogeneous 45 := by
  unfold a01793
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a01794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01791 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01793 ^ 1)
theorem ha01794 : a01794.IsHomogeneous 45 := by
  unfold a01794
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01791.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01793.pow 1)))

@[irreducible]
def a01795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01792 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01794 ^ 1)
theorem ha01795 : a01795.IsHomogeneous 45 := by
  unfold a01795
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01794.pow 1)))

@[irreducible]
def a01796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00264 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00721 ^ 1)
theorem ha01796 : a01796.IsHomogeneous 30 := by
  unfold a01796
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a01797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00766 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01796 ^ 1)
theorem ha01797 : a01797.IsHomogeneous 30 := by
  unfold a01797
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01796.pow 1)))

@[irreducible]
def a01798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00025 ^ 1 * a01721 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00721 ^ 1)
theorem ha01798 : a01798.IsHomogeneous 30 := by
  unfold a01798
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00025.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a01799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01796 ^ 1) + (C ((5 : ℂ) / (84 : ℂ)) * a01798 ^ 1)
theorem ha01799 : a01799.IsHomogeneous 30 := by
  unfold a01799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01796.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (84 : ℂ))).mul (ha01798.pow 1)))

@[irreducible]
def a01800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01797 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01799 ^ 1)
theorem ha01800 : a01800.IsHomogeneous 30 := by
  unfold a01800
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01799.pow 1)))

@[irreducible]
def a01801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01795 ^ 1) + (C ((7 : ℂ) / (432 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a01800 ^ 1)
theorem ha01801 : a01801.IsHomogeneous 45 := by
  unfold a01801
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01795.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (432 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha01800.pow 1)))

@[irreducible]
def a01802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00103 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a00762 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a00762 ^ 1)
theorem ha01802 : a01802.IsHomogeneous 94 := by
  unfold a01802
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha01801.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha00762.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a01803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01787 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a01802 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a01784 ^ 1)
theorem ha01803 : a01803.IsHomogeneous 94 := by
  unfold a01803
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01787.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha01802.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha01784.pow 1)))

@[irreducible]
def a01804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01786 ^ 1) + (C ((9 : ℂ) / (7 : ℂ)) * a01789 ^ 1) + (C ((9 : ℂ) / (7 : ℂ)) * a01803 ^ 1)
theorem ha01804 : a01804.IsHomogeneous 94 := by
  unfold a01804
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01786.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (7 : ℂ))).mul (ha01789.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (7 : ℂ))).mul (ha01803.pow 1)))

@[irreducible]
def a01805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00262 ^ 1 * a00769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a00283 ^ 1)
theorem ha01805 : a01805.IsHomogeneous 77 := by
  unfold a01805
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a01806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a00283 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00122 ^ 1 * a00262 ^ 1 * a00324 ^ 1)
theorem ha01806 : a01806.IsHomogeneous 77 := by
  unfold a01806
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00122.pow 1)).mul (ha00262.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a00717 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00122 ^ 1 * a01716 ^ 1)
theorem ha01807 : a01807.IsHomogeneous 77 := by
  unfold a01807
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha00717.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a01808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01807 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01806 ^ 1)
theorem ha01808 : a01808.IsHomogeneous 77 := by
  unfold a01808
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01805.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01807.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01806.pow 1)))

@[irreducible]
def a01809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00133 ^ 1 * a00769 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00133 ^ 1 * a00262 ^ 1 * a00283 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00283 ^ 1 * a00324 ^ 1)
theorem ha01809 : a01809.IsHomogeneous 79 := by
  unfold a01809
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00264 ^ 1)
theorem ha01810 : a01810.IsHomogeneous 25 := by
  unfold a01810
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)))

@[irreducible]
def a01811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha01811 : a01811.IsHomogeneous 25 := by
  unfold a01811
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a01812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01810 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01811 ^ 1)
theorem ha01812 : a01812.IsHomogeneous 25 := by
  unfold a01812
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01811.pow 1)))

@[irreducible]
def a01813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01721 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha01813 : a01813.IsHomogeneous 25 := by
  unfold a01813
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a01814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01811 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a01813 ^ 1)
theorem ha01814 : a01814.IsHomogeneous 25 := by
  unfold a01814
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01811.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha01813.pow 1)))

@[irreducible]
def a01815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01812 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01814 ^ 1)
theorem ha01815 : a01815.IsHomogeneous 25 := by
  unfold a01815
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01812.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01814.pow 1)))

@[irreducible]
def a01816 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01815 ^ 1)
theorem ha01816 : a01816.IsHomogeneous 25 := by
  unfold a01816
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha01469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01815.pow 1)))

@[irreducible]
def a01817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a00769 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00032 ^ 1 * a00103 ^ 1 * a01816 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00262 ^ 1 * a00769 ^ 1)
theorem ha01817 : a01817.IsHomogeneous 78 := by
  unfold a01817
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha01816.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a01818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01809 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01805 ^ 1)
theorem ha01818 : a01818.IsHomogeneous 79 := by
  unfold a01818
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01817.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01805.pow 1)))

@[irreducible]
def a01819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00122 ^ 1 * a00262 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00283 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00122 ^ 1)
theorem ha01819 : a01819.IsHomogeneous 79 := by
  unfold a01819
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00122.pow 1)).mul (ha00262.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00122.pow 1)))

@[irreducible]
def a01820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01806 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01809 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a01819 ^ 1)
theorem ha01820 : a01820.IsHomogeneous 79 := by
  unfold a01820
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01809.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha01819.pow 1)))

@[irreducible]
def a01821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01808 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01820 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a01818 ^ 1)
theorem ha01821 : a01821.IsHomogeneous 79 := by
  unfold a01821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01808.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01820.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha01818.pow 1)))

@[irreducible]
def a01822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a01782 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a01821 ^ 1) + (C ((35 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a01804 ^ 1)
theorem ha01822 : a01822.IsHomogeneous 95 := by
  unfold a01822
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha01782.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha01821.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha01804.pow 1)))

@[irreducible]
def a01823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00773 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a01822 ^ 1)
theorem ha01823 : a01823.IsHomogeneous 143 := by
  unfold a01823
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a01824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a01746 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01823 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01748 ^ 1)
theorem ha01824 : a01824.IsHomogeneous 185 := by
  unfold a01824
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha01746.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01823.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01748.pow 1)))

@[irreducible]
def a01825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a01747 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a01752 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01824 ^ 1)
theorem ha01825 : a01825.IsHomogeneous 185 := by
  unfold a01825
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha01747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha01752.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01824.pow 1)))

@[irreducible]
def a01826 : Poly := (C ((-5 : ℂ) / (1944 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a00775 ^ 1)
theorem ha01826 : a01826.IsHomogeneous 331 := by
  unfold a01826
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1944 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha00775.pow 1)))

@[irreducible]
def a01827 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a01826 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a01743 ^ 1)
theorem ha01827 : a01827.IsHomogeneous 435 := by
  unfold a01827
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha01826.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha01743.pow 1)))

@[irreducible]
def a01828 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1 * a00776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a01827 ^ 1)
theorem ha01828 : a01828.IsHomogeneous 514 := by
  unfold a01828
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).mul (ha00776.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha01827.pow 1)))

@[irreducible]
def a01829 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01828 ^ 1)
theorem ha01829 : a01829.IsHomogeneous 569 := by
  unfold a01829
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01828.pow 1)))

@[irreducible]
def a01830 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01741 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01829 ^ 1)
theorem ha01830 : a01830.IsHomogeneous 624 := by
  unfold a01830
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01741.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01829.pow 1)))

@[irreducible]
def a01831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01830 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00291 ^ 1 * a00778 ^ 1)
theorem ha01831 : a01831.IsHomogeneous 684 := by
  unfold a01831
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01830.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00291.pow 1)).mul (ha00778.pow 1)))

@[irreducible]
def a01832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01831 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a01711 ^ 1)
theorem ha01832 : a01832.IsHomogeneous 744 := by
  unfold a01832
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha01711.pow 1)))

@[irreducible]
def a01833 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 2)
theorem ha01833 : a01833.IsHomogeneous 436 := by
  unfold a01833
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 2)))

@[irreducible]
def a01834 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01833 ^ 1)
theorem ha01834 : a01834.IsHomogeneous 436 := by
  unfold a01834
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01833.pow 1)))

@[irreducible]
def a01835 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00290 ^ 1 * a00790 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00285 ^ 1 * a00787 ^ 1)
theorem ha01835 : a01835.IsHomogeneous 376 := by
  unfold a01835
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00290.pow 1)).mul (ha00790.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha00787.pow 1)))

@[irreducible]
def a01836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00783 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a00289 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00289 ^ 1)
theorem ha01836 : a01836.IsHomogeneous 119 := by
  unfold a01836
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00783.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)))

@[irreducible]
def a01837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00155 ^ 1 * a00265 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00785 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1)
theorem ha01837 : a01837.IsHomogeneous 176 := by
  unfold a01837
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00785.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)))

@[irreducible]
def a01838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha01838 : a01838.IsHomogeneous 6 := by
  unfold a01838
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha01839 : a01839.IsHomogeneous 6 := by
  unfold a01839
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01839 ^ 1)
theorem ha01840 : a01840.IsHomogeneous 6 := by
  unfold a01840
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01839.pow 1)))

@[irreducible]
def a01841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01838 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01840 ^ 1)
theorem ha01841 : a01841.IsHomogeneous 12 := by
  unfold a01841
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01838.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01840.pow 1)))

@[irreducible]
def a01842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a00289 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00155 ^ 1 * a00265 ^ 1)
theorem ha01842 : a01842.IsHomogeneous 127 := by
  unfold a01842
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01841.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)))

@[irreducible]
def a01843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01842 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a01836 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01837 ^ 1)
theorem ha01843 : a01843.IsHomogeneous 182 := by
  unfold a01843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01842.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01836.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01837.pow 1)))

@[irreducible]
def a01844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00783 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1)
theorem ha01844 : a01844.IsHomogeneous 174 := by
  unfold a01844
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)))

@[irreducible]
def a01845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((3 : ℂ) / (8 : ℂ)) * a00321 ^ 1)
theorem ha01845 : a01845.IsHomogeneous 6 := by
  unfold a01845
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00321.pow 1)))

@[irreducible]
def a01846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha01846 : a01846.IsHomogeneous 6 := by
  unfold a01846
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01846 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha01847 : a01847.IsHomogeneous 6 := by
  unfold a01847
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01848 : Poly := (C ((-1 : ℂ) / (155520 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 4 * a00012 ^ 4) + (C ((-1 : ℂ) / (466560 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00004 ^ 6 * a00005 ^ 3 * a00102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00102 ^ 2 * a01847 ^ 1) + (C ((7 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1) + (C ((7 : ℂ) / (270 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00005 ^ 3 * a00012 ^ 6 * a01845 ^ 1)
theorem ha01848 : a01848.IsHomogeneous 57 := by
  unfold a01848
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (155520 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 4)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (466560 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00102.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00102.pow 2)).mul (ha01847.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (270 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00005.pow 3)).mul (ha00012.pow 6)).mul (ha01845.pow 1)))

@[irreducible]
def a01849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00783 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a01848 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00783 ^ 1)
theorem ha01849 : a01849.IsHomogeneous 119 := by
  unfold a01849
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01848.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a01850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a01849 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01844 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a01836 ^ 1)
theorem ha01850 : a01850.IsHomogeneous 180 := by
  unfold a01850
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01849.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01844.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha01836.pow 1)))

@[irreducible]
def a01851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a01724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a00723 ^ 1)
theorem ha01851 : a01851.IsHomogeneous 109 := by
  unfold a01851
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha01724.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha00723.pow 1)))

@[irreducible]
def a01852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a00723 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01851 ^ 1)
theorem ha01852 : a01852.IsHomogeneous 109 := by
  unfold a01852
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha00723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01851.pow 1)))

@[irreducible]
def a01853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00124 ^ 1 * a00785 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a01852 ^ 1)
theorem ha01853 : a01853.IsHomogeneous 175 := by
  unfold a01853
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00124.pow 1)).mul (ha00785.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a01854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a01844 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01853 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01837 ^ 1)
theorem ha01854 : a01854.IsHomogeneous 181 := by
  unfold a01854
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha01844.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01853.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01837.pow 1)))

@[irreducible]
def a01855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a01850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01854 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 5 * a01843 ^ 1)
theorem ha01855 : a01855.IsHomogeneous 187 := by
  unfold a01855
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha01850.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01854.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 5)).mul (ha01843.pow 1)))

@[irreducible]
def a01856 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a00787 ^ 1)
theorem ha01856 : a01856.IsHomogeneous 285 := by
  unfold a01856
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01855.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha00787.pow 1)))

@[irreducible]
def a01857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a01856 ^ 1)
theorem ha01857 : a01857.IsHomogeneous 382 := by
  unfold a01857
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01835.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha01856.pow 1)))

@[irreducible]
def a01858 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 2)
theorem ha01858 : a01858.IsHomogeneous 194 := by
  unfold a01858
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a01859 : Poly := (C ((-108 : ℂ) / (5 : ℂ)) * a01858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1)
theorem ha01859 : a01859.IsHomogeneous 194 := by
  unfold a01859
  exact (((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (5 : ℂ))).mul (ha01858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)))

@[irreducible]
def a01860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00285 ^ 1 * a00773 ^ 1)
theorem ha01860 : a01860.IsHomogeneous 193 := by
  unfold a01860
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01822.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00285.pow 1)).mul (ha00773.pow 1)))

@[irreducible]
def a01861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00773 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01860 ^ 1)
theorem ha01861 : a01861.IsHomogeneous 193 := by
  unfold a01861
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01860.pow 1)))

@[irreducible]
def a01862 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00789 ^ 1)
theorem ha01862 : a01862.IsHomogeneous 291 := by
  unfold a01862
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00789.pow 1)))

@[irreducible]
def a01863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01859 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01862 ^ 1)
theorem ha01863 : a01863.IsHomogeneous 291 := by
  unfold a01863
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01859.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01862.pow 1)))

@[irreducible]
def a01864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00290 ^ 1 * a00790 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a01863 ^ 1)
theorem ha01864 : a01864.IsHomogeneous 412 := by
  unfold a01864
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00290.pow 1)).mul (ha00790.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01863.pow 1)))

@[irreducible]
def a01865 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a01864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a01835 ^ 1)
theorem ha01865 : a01865.IsHomogeneous 473 := by
  unfold a01865
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha01835.pow 1)))

@[irreducible]
def a01866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a01857 ^ 1)
theorem ha01866 : a01866.IsHomogeneous 479 := by
  unfold a01866
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha01857.pow 1)))

@[irreducible]
def a01867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a00792 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1)
theorem ha01867 : a01867.IsHomogeneous 594 := by
  unfold a01867
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha00792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a01868 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00124 ^ 1 * a01867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a01834 ^ 1)
theorem ha01868 : a01868.IsHomogeneous 654 := by
  unfold a01868
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00124.pow 1)).mul (ha01867.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha01834.pow 1)))

@[irreducible]
def a01869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1 * a00793 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a01868 ^ 1)
theorem ha01869 : a01869.IsHomogeneous 720 := by
  unfold a01869
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).mul (ha00793.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha01868.pow 1)))

@[irreducible]
def a01870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01711 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a01869 ^ 1)
theorem ha01870 : a01870.IsHomogeneous 762 := by
  unfold a01870
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01711.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha01869.pow 1)))

@[irreducible]
def a01871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01832 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a01870 ^ 1)
theorem ha01871 : a01871.IsHomogeneous 804 := by
  unfold a01871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01832.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha01870.pow 1)))

@[irreducible]
def a01872 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00294 ^ 1 * a00795 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a01871 ^ 1)
theorem ha01872 : a01872.IsHomogeneous 909 := by
  unfold a01872
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00294.pow 1)).mul (ha00795.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a01873 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01872 ^ 1)
theorem ha01873 : a01873.IsHomogeneous 909 := by
  unfold a01873
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01710.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01872.pow 1)))

@[irreducible]
def a01874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00293 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00260 ^ 1 * a00798 ^ 1)
theorem ha01874 : a01874.IsHomogeneous 122 := by
  unfold a01874
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00293.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00260.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a01875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a01702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a00712 ^ 1)
theorem ha01875 : a01875.IsHomogeneous 120 := by
  unfold a01875
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a01876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01875 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a01874 ^ 1)
theorem ha01876 : a01876.IsHomogeneous 122 := by
  unfold a01876
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha01874.pow 1)))

@[irreducible]
def a01877 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 1 * a01507 ^ 1) + (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a01581 ^ 1) + (C ((-1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 5 * a00005 ^ 4 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a01433 ^ 1) + (C ((1 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a01678 ^ 1)
theorem ha01877 : a01877.IsHomogeneous 79 := by
  unfold a01877
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 1)).mul (ha01507.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha01581.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha01702.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha01433.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a01878 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a00798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a01877 ^ 1)
theorem ha01878 : a01878.IsHomogeneous 122 := by
  unfold a01878
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha00798.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a01879 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a01878 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01874 ^ 1)
theorem ha01879 : a01879.IsHomogeneous 122 := by
  unfold a01879
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha01878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01874.pow 1)))

@[irreducible]
def a01880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01876 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a01879 ^ 1)
theorem ha01880 : a01880.IsHomogeneous 122 := by
  unfold a01880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01876.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha01879.pow 1)))

@[irreducible]
def a01881 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a00800 ^ 1)
theorem ha01881 : a01881.IsHomogeneous 401 := by
  unfold a01881
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha00800.pow 1)))

@[irreducible]
def a01882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01710 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01881 ^ 1)
theorem ha01882 : a01882.IsHomogeneous 655 := by
  unfold a01882
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01710.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01881.pow 1)))

@[irreducible]
def a01883 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01882 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01873 ^ 1)
theorem ha01883 : a01883.IsHomogeneous 909 := by
  unfold a01883
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01873.pow 1)))

@[irreducible]
def a01884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a00802 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a01883 ^ 1)
theorem ha01884 : a01884.IsHomogeneous 988 := by
  unfold a01884
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha00802.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha01883.pow 1)))

@[irreducible]
def a01885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01319 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a01884 ^ 1)
theorem ha01885 : a01885.IsHomogeneous 1067 := by
  unfold a01885
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01319.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha01884.pow 1)))

@[irreducible]
def a01886 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a01885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01709 ^ 1)
theorem ha01886 : a01886.IsHomogeneous 1146 := by
  unfold a01886
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha01885.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01709.pow 1)))

@[irreducible]
def a01887 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a00804 ^ 1)
theorem ha01887 : a01887.IsHomogeneous 1254 := by
  unfold a01887
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01886.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha00804.pow 1)))

@[irreducible]
def a01888 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a01887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01318 ^ 1)
theorem ha01888 : a01888.IsHomogeneous 1344 := by
  unfold a01888
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01887.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01318.pow 1)))

@[irreducible]
def a01889 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a00825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00304 ^ 1 * a00834 ^ 1)
theorem ha01889 : a01889.IsHomogeneous 276 := by
  unfold a01889
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha00825.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00304.pow 1)).mul (ha00834.pow 1)))

@[irreducible]
def a01890 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00298 ^ 1 * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00303 ^ 1 * a00809 ^ 1)
theorem ha01890 : a01890.IsHomogeneous 150 := by
  unfold a01890
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00298.pow 1)).mul (ha00823.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha01891 : a01891.IsHomogeneous 27 := by
  unfold a01891
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a01892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01891 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00615 ^ 1)
theorem ha01892 : a01892.IsHomogeneous 27 := by
  unfold a01892
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01891.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00615.pow 1)))

@[irreducible]
def a01893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1)
theorem ha01893 : a01893.IsHomogeneous 27 := by
  unfold a01893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01891 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01893 ^ 1)
theorem ha01894 : a01894.IsHomogeneous 27 := by
  unfold a01894
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01893.pow 1)))

@[irreducible]
def a01895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01892 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01894 ^ 1)
theorem ha01895 : a01895.IsHomogeneous 27 := by
  unfold a01895
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01894.pow 1)))

@[irreducible]
def a01896 : Poly := (C ((-7 : ℂ) / (4860 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01895 ^ 1)
theorem ha01896 : a01896.IsHomogeneous 27 := by
  unfold a01896
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (4860 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01895.pow 1)))

@[irreducible]
def a01897 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a00809 ^ 1)
theorem ha01897 : a01897.IsHomogeneous 141 := by
  unfold a01897
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01897 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01890 ^ 1)
theorem ha01898 : a01898.IsHomogeneous 150 := by
  unfold a01898
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01897.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01890.pow 1)))

@[irreducible]
def a01899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00302 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00821 ^ 1)
theorem ha01899 : a01899.IsHomogeneous 120 := by
  unfold a01899
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00302.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00821.pow 1)))

@[irreducible]
def a01900 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01841 ^ 1)
theorem ha01900 : a01900.IsHomogeneous 120 := by
  unfold a01900
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00302.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a01901 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a01900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01899 ^ 1)
theorem ha01901 : a01901.IsHomogeneous 120 := by
  unfold a01901
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha01900.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01899.pow 1)))

@[irreducible]
def a01902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a00819 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a00812 ^ 1)
theorem ha01902 : a01902.IsHomogeneous 117 := by
  unfold a01902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha00819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a01903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a01847 ^ 1) + (C ((1 : ℂ) / (2160 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha01903 : a01903.IsHomogeneous 15 := by
  unfold a01903
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha01847.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2160 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a01904 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a00812 ^ 1)
theorem ha01904 : a01904.IsHomogeneous 111 := by
  unfold a01904
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a01905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01902 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01904 ^ 1)
theorem ha01905 : a01905.IsHomogeneous 117 := by
  unfold a01905
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01902.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01904.pow 1)))

@[irreducible]
def a01906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a00817 ^ 1)
theorem ha01906 : a01906.IsHomogeneous 99 := by
  unfold a01906
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha00712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a01907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00300 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a01702 ^ 1)
theorem ha01907 : a01907.IsHomogeneous 105 := by
  unfold a01907
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00300.pow 1)).mul (ha00712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a01908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01906 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01907 ^ 1)
theorem ha01908 : a01908.IsHomogeneous 105 := by
  unfold a01908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01907.pow 1)))

@[irreducible]
def a01909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha01909 : a01909.IsHomogeneous 51 := by
  unfold a01909
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha01910 : a01910.IsHomogeneous 51 := by
  unfold a01910
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01909 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a01910 ^ 1)
theorem ha01911 : a01911.IsHomogeneous 51 := by
  unfold a01911
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01909.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha01910.pow 1)))

@[irreducible]
def a01912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha01912 : a01912.IsHomogeneous 51 := by
  unfold a01912
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01909 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01912 ^ 1)
theorem ha01913 : a01913.IsHomogeneous 51 := by
  unfold a01913
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01909.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01912.pow 1)))

@[irreducible]
def a01914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01913 ^ 1)
theorem ha01914 : a01914.IsHomogeneous 51 := by
  unfold a01914
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01913.pow 1)))

@[irreducible]
def a01915 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a01914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00817 ^ 1)
theorem ha01915 : a01915.IsHomogeneous 93 := by
  unfold a01915
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a01916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01906 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01915 ^ 1)
theorem ha01916 : a01916.IsHomogeneous 99 := by
  unfold a01916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01906.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01915.pow 1)))

@[irreducible]
def a01917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01908 ^ 1)
theorem ha01917 : a01917.IsHomogeneous 105 := by
  unfold a01917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01916.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01908.pow 1)))

@[irreducible]
def a01918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00299 ^ 1 * a00819 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00127 ^ 1 * a01917 ^ 1)
theorem ha01918 : a01918.IsHomogeneous 123 := by
  unfold a01918
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00819.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00127.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a01919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01902 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01918 ^ 1)
theorem ha01919 : a01919.IsHomogeneous 123 := by
  unfold a01919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01918.pow 1)))

@[irreducible]
def a01920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01919 ^ 1)
theorem ha01920 : a01920.IsHomogeneous 123 := by
  unfold a01920
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01919.pow 1)))

@[irreducible]
def a01921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01920 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00821 ^ 1)
theorem ha01921 : a01921.IsHomogeneous 123 := by
  unfold a01921
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01920.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00821.pow 1)))

@[irreducible]
def a01922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01921 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a01899 ^ 1)
theorem ha01922 : a01922.IsHomogeneous 123 := by
  unfold a01922
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01921.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha01899.pow 1)))

@[irreducible]
def a01923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01922 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a01901 ^ 1)
theorem ha01923 : a01923.IsHomogeneous 123 := by
  unfold a01923
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01922.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha01901.pow 1)))

@[irreducible]
def a01924 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a01923 ^ 1)
theorem ha01924 : a01924.IsHomogeneous 156 := by
  unfold a01924
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00823.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a01925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01924 ^ 1)
theorem ha01925 : a01925.IsHomogeneous 156 := by
  unfold a01925
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01924.pow 1)))

@[irreducible]
def a01926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01898 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01925 ^ 1)
theorem ha01926 : a01926.IsHomogeneous 156 := by
  unfold a01926
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01925.pow 1)))

@[irreducible]
def a01927 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01926 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00825 ^ 1)
theorem ha01927 : a01927.IsHomogeneous 216 := by
  unfold a01927
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00825.pow 1)))

@[irreducible]
def a01928 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01889 ^ 1)
theorem ha01928 : a01928.IsHomogeneous 276 := by
  unfold a01928
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01889.pow 1)))

@[irreducible]
def a01929 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 2)
theorem ha01929 : a01929.IsHomogeneous 132 := by
  unfold a01929
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 2)))

@[irreducible]
def a01930 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01929 ^ 1)
theorem ha01930 : a01930.IsHomogeneous 132 := by
  unfold a01930
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01929.pow 1)))

@[irreducible]
def a01931 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00831 ^ 1)
theorem ha01931 : a01931.IsHomogeneous 105 := by
  unfold a01931
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a01932 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00317 ^ 1)
theorem ha01932 : a01932.IsHomogeneous 63 := by
  unfold a01932
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01933 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a01932 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01931 ^ 1)
theorem ha01933 : a01933.IsHomogeneous 105 := by
  unfold a01933
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01931.pow 1)))

@[irreducible]
def a01934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1)
theorem ha01934 : a01934.IsHomogeneous 84 := by
  unfold a01934
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a01935 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1)
theorem ha01935 : a01935.IsHomogeneous 87 := by
  unfold a01935
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a01936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01934 ^ 1)
theorem ha01936 : a01936.IsHomogeneous 126 := by
  unfold a01936
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01934.pow 1)))

@[irreducible]
def a01937 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01702 ^ 1)
theorem ha01937 : a01937.IsHomogeneous 87 := by
  unfold a01937
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a01938 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a01937 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1)
theorem ha01938 : a01938.IsHomogeneous 87 := by
  unfold a01938
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha01937.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a01939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a00829 ^ 1)
theorem ha01939 : a01939.IsHomogeneous 126 := by
  unfold a01939
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a01940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01934 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01939 ^ 1)
theorem ha01940 : a01940.IsHomogeneous 126 := by
  unfold a01940
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01939.pow 1)))

@[irreducible]
def a01941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01940 ^ 1)
theorem ha01941 : a01941.IsHomogeneous 126 := by
  unfold a01941
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01940.pow 1)))

@[irreducible]
def a01942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00129 ^ 1 * a00831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01941 ^ 1)
theorem ha01942 : a01942.IsHomogeneous 150 := by
  unfold a01942
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).mul (ha00831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a01943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a01931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01942 ^ 1)
theorem ha01943 : a01943.IsHomogeneous 150 := by
  unfold a01943
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01942.pow 1)))

@[irreducible]
def a01944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a01933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01943 ^ 1)
theorem ha01944 : a01944.IsHomogeneous 150 := by
  unfold a01944
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01933.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01943.pow 1)))

@[irreducible]
def a01945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a01944 ^ 1)
theorem ha01945 : a01945.IsHomogeneous 174 := by
  unfold a01945
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a01946 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a01945 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01930 ^ 1)
theorem ha01946 : a01946.IsHomogeneous 198 := by
  unfold a01946
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha01945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01930.pow 1)))

@[irreducible]
def a01947 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1 * a00834 ^ 1)
theorem ha01947 : a01947.IsHomogeneous 246 := by
  unfold a01947
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01946.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)).mul (ha00834.pow 1)))

@[irreducible]
def a01948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01889 ^ 1)
theorem ha01948 : a01948.IsHomogeneous 276 := by
  unfold a01948
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01889.pow 1)))

@[irreducible]
def a01949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01928 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01948 ^ 1)
theorem ha01949 : a01949.IsHomogeneous 276 := by
  unfold a01949
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01948.pow 1)))

@[irreducible]
def a01950 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a00836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01949 ^ 1)
theorem ha01950 : a01950.IsHomogeneous 702 := by
  unfold a01950
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha00836.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a01951 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01318 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01950 ^ 1)
theorem ha01951 : a01951.IsHomogeneous 1035 := by
  unfold a01951
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01318.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01950.pow 1)))

@[irreducible]
def a01952 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01888 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01951 ^ 1)
theorem ha01952 : a01952.IsHomogeneous 1368 := by
  unfold a01952
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01888.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01951.pow 1)))

@[irreducible]
def a01953 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00850 ^ 1)
theorem ha01953 : a01953.IsHomogeneous 963 := by
  unfold a01953
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a01954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a00804 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01886 ^ 1)
theorem ha01954 : a01954.IsHomogeneous 1230 := by
  unfold a01954
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha00804.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a01955 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a01954 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01953 ^ 1)
theorem ha01955 : a01955.IsHomogeneous 1296 := by
  unfold a01955
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01954.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01953.pow 1)))

@[irreducible]
def a01956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00309 ^ 1 * a00848 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a00846 ^ 1)
theorem ha01956 : a01956.IsHomogeneous 168 := by
  unfold a01956
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00309.pow 1)).mul (ha00848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00846.pow 1)))

@[irreducible]
def a01957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1 * a00308 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00843 ^ 1)
theorem ha01957 : a01957.IsHomogeneous 84 := by
  unfold a01957
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1)).mul (ha00308.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00843.pow 1)))

@[irreducible]
def a01958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a00812 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00299 ^ 1 * a00841 ^ 1)
theorem ha01958 : a01958.IsHomogeneous 75 := by
  unfold a01958
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00299.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a01959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00812 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00126 ^ 1 * a01903 ^ 1)
theorem ha01959 : a01959.IsHomogeneous 45 := by
  unfold a01959
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00126.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a01960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01958 ^ 1)
theorem ha01960 : a01960.IsHomogeneous 75 := by
  unfold a01960
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01959.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01958.pow 1)))

@[irreducible]
def a01961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01896 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00809 ^ 1)
theorem ha01961 : a01961.IsHomogeneous 57 := by
  unfold a01961
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a01961 ^ 1)
theorem ha01962 : a01962.IsHomogeneous 57 := by
  unfold a01962
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha01961.pow 1)))

@[irreducible]
def a01963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a01962 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00299 ^ 1 * a00841 ^ 1)
theorem ha01963 : a01963.IsHomogeneous 75 := by
  unfold a01963
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha01962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00299.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a01964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01958 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a01963 ^ 1)
theorem ha01964 : a01964.IsHomogeneous 75 := by
  unfold a01964
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01958.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha01963.pow 1)))

@[irreducible]
def a01965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01964 ^ 1)
theorem ha01965 : a01965.IsHomogeneous 75 := by
  unfold a01965
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01964.pow 1)))

@[irreducible]
def a01966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01965 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00843 ^ 1)
theorem ha01966 : a01966.IsHomogeneous 81 := by
  unfold a01966
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01965.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00843.pow 1)))

@[irreducible]
def a01967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01966 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01957 ^ 1)
theorem ha01967 : a01967.IsHomogeneous 87 := by
  unfold a01967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01966.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01957.pow 1)))

@[irreducible]
def a01968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a01841 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00308 ^ 1)
theorem ha01968 : a01968.IsHomogeneous 60 := by
  unfold a01968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00308.pow 1)))

@[irreducible]
def a01969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01968 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01957 ^ 1)
theorem ha01969 : a01969.IsHomogeneous 90 := by
  unfold a01969
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01968.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01957.pow 1)))

@[irreducible]
def a01970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01967 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01969 ^ 1)
theorem ha01970 : a01970.IsHomogeneous 93 := by
  unfold a01970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01967.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01969.pow 1)))

@[irreducible]
def a01971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00846 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01970 ^ 1)
theorem ha01971 : a01971.IsHomogeneous 132 := by
  unfold a01971
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00846.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01970.pow 1)))

@[irreducible]
def a01972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01956 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a01971 ^ 1)
theorem ha01972 : a01972.IsHomogeneous 168 := by
  unfold a01972
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha01971.pow 1)))

@[irreducible]
def a01973 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00829 ^ 1)
theorem ha01973 : a01973.IsHomogeneous 126 := by
  unfold a01973
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a01974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (6 : ℂ)) * a00829 ^ 1)
theorem ha01974 : a01974.IsHomogeneous 84 := by
  unfold a01974
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a01975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01974 ^ 1)
theorem ha01975 : a01975.IsHomogeneous 84 := by
  unfold a01975
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01974.pow 1)))

@[irreducible]
def a01976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01975 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01973 ^ 1)
theorem ha01976 : a01976.IsHomogeneous 126 := by
  unfold a01976
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01973.pow 1)))

@[irreducible]
def a01977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a01976 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00309 ^ 1 * a00848 ^ 1)
theorem ha01977 : a01977.IsHomogeneous 174 := by
  unfold a01977
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01976.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00309.pow 1)).mul (ha00848.pow 1)))

@[irreducible]
def a01978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01977 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01956 ^ 1)
theorem ha01978 : a01978.IsHomogeneous 204 := by
  unfold a01978
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01977.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01956.pow 1)))

@[irreducible]
def a01979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01978 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01972 ^ 1)
theorem ha01979 : a01979.IsHomogeneous 204 := by
  unfold a01979
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01972.pow 1)))

@[irreducible]
def a01980 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a00850 ^ 1)
theorem ha01980 : a01980.IsHomogeneous 630 := by
  unfold a01980
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01979.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a01981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01980 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01953 ^ 1)
theorem ha01981 : a01981.IsHomogeneous 963 := by
  unfold a01981
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01980.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01953.pow 1)))

@[irreducible]
def a01982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01981 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01955 ^ 1)
theorem ha01982 : a01982.IsHomogeneous 1296 := by
  unfold a01982
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01955.pow 1)))

@[irreducible]
def a01983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01952 ^ 1) + (C ((64 : ℂ) / (27 : ℂ)) * a00042 ^ 3 * a01982 ^ 1)
theorem ha01983 : a01983.IsHomogeneous 1368 := by
  unfold a01983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01952.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (27 : ℂ))).mul (ha00042.pow 3)).mul (ha01982.pow 1)))

@[irreducible]
def a01984 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a00853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01983 ^ 1)
theorem ha01984 : a01984.IsHomogeneous 1428 := by
  unfold a01984
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha00853.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01983.pow 1)))

@[irreducible]
def a01985 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01984 ^ 1)
theorem ha01985 : a01985.IsHomogeneous 1488 := by
  unfold a01985
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01984.pow 1)))

@[irreducible]
def a01986 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 2)
theorem ha01986 : a01986.IsHomogeneous 204 := by
  unfold a01986
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 2)))

@[irreducible]
def a01987 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01986 ^ 1)
theorem ha01987 : a01987.IsHomogeneous 204 := by
  unfold a01987
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01986.pow 1)))

@[irreducible]
def a01988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00326 ^ 1 * a00878 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00876 ^ 1)
theorem ha01988 : a01988.IsHomogeneous 141 := by
  unfold a01988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00326.pow 1)).mul (ha00878.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00876.pow 1)))

@[irreducible]
def a01989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha01989 : a01989.IsHomogeneous 51 := by
  unfold a01989
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00809 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00298 ^ 1)
theorem ha01990 : a01990.IsHomogeneous 54 := by
  unfold a01990
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00809.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha01991 : a01991.IsHomogeneous 54 := by
  unfold a01991
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01989 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01990 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a01991 ^ 1)
theorem ha01992 : a01992.IsHomogeneous 54 := by
  unfold a01992
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01989.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01990.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha01991.pow 1)))

@[irreducible]
def a01993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha01993 : a01993.IsHomogeneous 51 := by
  unfold a01993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha01994 : a01994.IsHomogeneous 51 := by
  unfold a01994
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01989 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a01994 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01993 ^ 1)
theorem ha01995 : a01995.IsHomogeneous 51 := by
  unfold a01995
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01989.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha01994.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01993.pow 1)))

@[irreducible]
def a01996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha01996 : a01996.IsHomogeneous 51 := by
  unfold a01996
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a01997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01990 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01996 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01993 ^ 1)
theorem ha01997 : a01997.IsHomogeneous 54 := by
  unfold a01997
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01990.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01996.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01993.pow 1)))

@[irreducible]
def a01998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01995 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01997 ^ 1)
theorem ha01998 : a01998.IsHomogeneous 54 := by
  unfold a01998
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01995.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01992.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01997.pow 1)))

@[irreducible]
def a01999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a00655 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00218 ^ 1 * a00865 ^ 1)
theorem ha01999 : a01999.IsHomogeneous 57 := by
  unfold a01999
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha00655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00218.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a02000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00655 ^ 1)
theorem ha02000 : a02000.IsHomogeneous 54 := by
  unfold a02000
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a02001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02000 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01999 ^ 1)
theorem ha02001 : a02001.IsHomogeneous 57 := by
  unfold a02001
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02000.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01999.pow 1)))

@[irreducible]
def a02002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00504 ^ 1)
theorem ha02002 : a02002.IsHomogeneous 6 := by
  unfold a02002
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00504.pow 1)))

@[irreducible]
def a02003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01324 ^ 1)
theorem ha02003 : a02003.IsHomogeneous 6 := by
  unfold a02003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01324.pow 1)))

@[irreducible]
def a02004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02002 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a02003 ^ 1)
theorem ha02004 : a02004.IsHomogeneous 6 := by
  unfold a02004
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02002.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha02003.pow 1)))

@[irreducible]
def a02005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha02005 : a02005.IsHomogeneous 6 := by
  unfold a02005
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a02006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02005 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02002 ^ 1)
theorem ha02006 : a02006.IsHomogeneous 12 := by
  unfold a02006
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02005.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02002.pow 1)))

@[irreducible]
def a02007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02006 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02004 ^ 1)
theorem ha02007 : a02007.IsHomogeneous 12 := by
  unfold a02007
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02004.pow 1)))

@[irreducible]
def a02008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (135 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3)
theorem ha02008 : a02008.IsHomogeneous 18 := by
  unfold a02008
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (135 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a02009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00064 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00865 ^ 1)
theorem ha02009 : a02009.IsHomogeneous 57 := by
  unfold a02009
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a02010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01999 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a02009 ^ 1)
theorem ha02010 : a02010.IsHomogeneous 57 := by
  unfold a02010
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha02009.pow 1)))

@[irreducible]
def a02011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02001 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02010 ^ 1)
theorem ha02011 : a02011.IsHomogeneous 57 := by
  unfold a02011
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02010.pow 1)))

@[irreducible]
def a02012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00201 ^ 1)
theorem ha02012 : a02012.IsHomogeneous 54 := by
  unfold a02012
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a02013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha02013 : a02013.IsHomogeneous 51 := by
  unfold a02013
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a02014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a00317 ^ 1)
theorem ha02014 : a02014.IsHomogeneous 57 := by
  unfold a02014
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a02015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02014 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a02013 ^ 1)
theorem ha02015 : a02015.IsHomogeneous 57 := by
  unfold a02015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha02013.pow 1)))

@[irreducible]
def a02016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha02016 : a02016.IsHomogeneous 51 := by
  unfold a02016
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a02017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00621 ^ 1)
theorem ha02017 : a02017.IsHomogeneous 57 := by
  unfold a02017
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a02018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02017 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a02016 ^ 1)
theorem ha02018 : a02018.IsHomogeneous 57 := by
  unfold a02018
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02017.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha02016.pow 1)))

@[irreducible]
def a02019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00201 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00129 ^ 1)
theorem ha02019 : a02019.IsHomogeneous 54 := by
  unfold a02019
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02019 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a02013 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a02016 ^ 1)
theorem ha02020 : a02020.IsHomogeneous 54 := by
  unfold a02020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02019.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha02013.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha02016.pow 1)))

@[irreducible]
def a02021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02020 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a02015 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a02018 ^ 1)
theorem ha02021 : a02021.IsHomogeneous 57 := by
  unfold a02021
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha02015.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha02018.pow 1)))

@[irreducible]
def a02022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00317 ^ 1)
theorem ha02022 : a02022.IsHomogeneous 39 := by
  unfold a02022
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a02023 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00129 ^ 1)
theorem ha02023 : a02023.IsHomogeneous 39 := by
  unfold a02023
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02024 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00058 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha02024 : a02024.IsHomogeneous 39 := by
  unfold a02024
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a02025 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a02023 ^ 1) + (C ((-5 : ℂ) / (42 : ℂ)) * a02024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02022 ^ 1)
theorem ha02025 : a02025.IsHomogeneous 39 := by
  unfold a02025
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha02023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (42 : ℂ))).mul (ha02024.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02022.pow 1)))

@[irreducible]
def a02026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha02026 : a02026.IsHomogeneous 42 := by
  unfold a02026
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a02027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha02027 : a02027.IsHomogeneous 42 := by
  unfold a02027
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a02028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02022 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02027 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02026 ^ 1)
theorem ha02028 : a02028.IsHomogeneous 42 := by
  unfold a02028
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02022.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02027.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02026.pow 1)))

@[irreducible]
def a02029 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1)
theorem ha02029 : a02029.IsHomogeneous 36 := by
  unfold a02029
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02030 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a02026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02023 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a02029 ^ 1)
theorem ha02030 : a02030.IsHomogeneous 42 := by
  unfold a02030
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha02026.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02023.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha02029.pow 1)))

@[irreducible]
def a02031 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a02030 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02028 ^ 1)
theorem ha02031 : a02031.IsHomogeneous 42 := by
  unfold a02031
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha02030.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02028.pow 1)))

@[irreducible]
def a02032 : Poly := (C ((-7 : ℂ) / (6 : ℂ)) * a02021 ^ 1) + (C ((-7 : ℂ) / (180 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a02031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01998 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a02011 ^ 1)
theorem ha02032 : a02032.IsHomogeneous 57 := by
  unfold a02032
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (6 : ℂ))).mul (ha02021.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (180 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha02031.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01998.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha02011.pow 1)))

@[irreducible]
def a02033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00876 ^ 1) + (C ((4 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02032 ^ 1)
theorem ha02033 : a02033.IsHomogeneous 99 := by
  unfold a02033
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00876.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02032.pow 1)))

@[irreducible]
def a02034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01988 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02033 ^ 1)
theorem ha02034 : a02034.IsHomogeneous 141 := by
  unfold a02034
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01988.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02033.pow 1)))

@[irreducible]
def a02035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a01702 ^ 1)
theorem ha02035 : a02035.IsHomogeneous 87 := by
  unfold a02035
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a02036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha02036 : a02036.IsHomogeneous 84 := by
  unfold a02036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02036 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha02037 : a02037.IsHomogeneous 84 := by
  unfold a02037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02036.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02037 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a02035 ^ 1)
theorem ha02038 : a02038.IsHomogeneous 126 := by
  unfold a02038
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02037.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha02035.pow 1)))

@[irreducible]
def a02039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a02038 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00326 ^ 1 * a00878 ^ 1)
theorem ha02039 : a02039.IsHomogeneous 186 := by
  unfold a02039
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha02038.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00326.pow 1)).mul (ha00878.pow 1)))

@[irreducible]
def a02040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02039 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a01988 ^ 1)
theorem ha02040 : a02040.IsHomogeneous 186 := by
  unfold a02040
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02039.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01988.pow 1)))

@[irreducible]
def a02041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02040 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a02034 ^ 1)
theorem ha02041 : a02041.IsHomogeneous 186 := by
  unfold a02041
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02040.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02034.pow 1)))

@[irreducible]
def a02042 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00880 ^ 1)
theorem ha02042 : a02042.IsHomogeneous 246 := by
  unfold a02042
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a02043 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a02042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a01987 ^ 1)
theorem ha02043 : a02043.IsHomogeneous 306 := by
  unfold a02043
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha02042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha01987.pow 1)))

@[irreducible]
def a02044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1 * a00881 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02043 ^ 1)
theorem ha02044 : a02044.IsHomogeneous 804 := by
  unfold a02044
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).mul (ha00881.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02043.pow 1)))

@[irreducible]
def a02045 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a02044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01317 ^ 1)
theorem ha02045 : a02045.IsHomogeneous 1191 := by
  unfold a02045
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha02044.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01317.pow 1)))

@[irreducible]
def a02046 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01985 ^ 1)
theorem ha02046 : a02046.IsHomogeneous 1548 := by
  unfold a02046
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02045.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01985.pow 1)))

@[irreducible]
def a02047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00930 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a00878 ^ 1)
theorem ha02047 : a02047.IsHomogeneous 187 := by
  unfold a02047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00930.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha00878.pow 1)))

end CycleQ2Concrete
