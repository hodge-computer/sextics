import Proposal.CurrentAtoms000

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a00512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a00511 ^ 1)
theorem ha00512 : a00512.IsHomogeneous 18 := by
  unfold a00512
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha00511.pow 1)))

@[irreducible]
def a00513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00512 ^ 1)
theorem ha00513 : a00513.IsHomogeneous 18 := by
  unfold a00513
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00512.pow 1)))

@[irreducible]
def a00514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00157 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00513 ^ 1)
theorem ha00514 : a00514.IsHomogeneous 18 := by
  unfold a00514
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)))

@[irreducible]
def a00515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00507 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00514 ^ 1)
theorem ha00515 : a00515.IsHomogeneous 18 := by
  unfold a00515
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00514.pow 1)))

@[irreducible]
def a00516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha00516 : a00516.IsHomogeneous 12 := by
  unfold a00516
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a00517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1)
theorem ha00517 : a00517.IsHomogeneous 18 := by
  unfold a00517
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a00518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha00518 : a00518.IsHomogeneous 6 := by
  unfold a00518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha00519 : a00519.IsHomogeneous 12 := by
  unfold a00519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a00520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00519 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00518 ^ 1)
theorem ha00520 : a00520.IsHomogeneous 12 := by
  unfold a00520
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00519.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00518.pow 1)))

@[irreducible]
def a00521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1)
theorem ha00521 : a00521.IsHomogeneous 18 := by
  unfold a00521
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a00522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00517 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00521 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00516 ^ 1)
theorem ha00522 : a00522.IsHomogeneous 18 := by
  unfold a00522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00517.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00521.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00516.pow 1)))

@[irreducible]
def a00523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00007 ^ 2 * a00522 ^ 1) + (C ((2 : ℂ) / (405 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00005 ^ 3 * a00515 ^ 1)
theorem ha00523 : a00523.IsHomogeneous 33 := by
  unfold a00523
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00007.pow 2)).mul (ha00522.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00005.pow 3)).mul (ha00515.pow 1)))

@[irreducible]
def a00524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00161 ^ 1)
theorem ha00524 : a00524.IsHomogeneous 24 := by
  unfold a00524
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00161.pow 1)))

@[irreducible]
def a00525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha00525 : a00525.IsHomogeneous 12 := by
  unfold a00525
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a00526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha00526 : a00526.IsHomogeneous 12 := by
  unfold a00526
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a00527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1)
theorem ha00527 : a00527.IsHomogeneous 18 := by
  unfold a00527
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00527 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00525 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00526 ^ 1)
theorem ha00528 : a00528.IsHomogeneous 18 := by
  unfold a00528
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00527.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00525.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00526.pow 1)))

@[irreducible]
def a00529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00161 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00528 ^ 1)
theorem ha00529 : a00529.IsHomogeneous 24 := by
  unfold a00529
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00161.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)))

@[irreducible]
def a00530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00524 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00529 ^ 1)
theorem ha00530 : a00530.IsHomogeneous 24 := by
  unfold a00530
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00529.pow 1)))

@[irreducible]
def a00531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00157 ^ 1)
theorem ha00531 : a00531.IsHomogeneous 12 := by
  unfold a00531
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00157.pow 1)))

@[irreducible]
def a00532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00157 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00513 ^ 1)
theorem ha00532 : a00532.IsHomogeneous 18 := by
  unfold a00532
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00513.pow 1)))

@[irreducible]
def a00533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00531 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00532 ^ 1)
theorem ha00533 : a00533.IsHomogeneous 18 := by
  unfold a00533
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00531.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00532.pow 1)))

@[irreducible]
def a00534 : Poly := (C ((-1 : ℂ) / (30 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00533 ^ 1)
theorem ha00534 : a00534.IsHomogeneous 37 := by
  unfold a00534
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (30 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00530.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00533.pow 1)))

@[irreducible]
def a00535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1)
theorem ha00535 : a00535.IsHomogeneous 18 := by
  unfold a00535
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00155 ^ 1)
theorem ha00536 : a00536.IsHomogeneous 24 := by
  unfold a00536
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00520 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1)
theorem ha00537 : a00537.IsHomogeneous 18 := by
  unfold a00537
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00536 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00537 ^ 1)
theorem ha00538 : a00538.IsHomogeneous 24 := by
  unfold a00538
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00536.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00537.pow 1)))

@[irreducible]
def a00539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00037 ^ 1 * a00130 ^ 1)
theorem ha00539 : a00539.IsHomogeneous 18 := by
  unfold a00539
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00037.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00037 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00168 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1)
theorem ha00540 : a00540.IsHomogeneous 18 := by
  unfold a00540
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1)
theorem ha00541 : a00541.IsHomogeneous 6 := by
  unfold a00541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1)
theorem ha00542 : a00542.IsHomogeneous 18 := by
  unfold a00542
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a00543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00542 ^ 1)
theorem ha00543 : a00543.IsHomogeneous 18 := by
  unfold a00543
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00542.pow 1)))

@[irreducible]
def a00544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00510 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00156 ^ 1)
theorem ha00544 : a00544.IsHomogeneous 18 := by
  unfold a00544
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00156 ^ 1)
theorem ha00545 : a00545.IsHomogeneous 12 := by
  unfold a00545
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00545 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00544 ^ 1)
theorem ha00546 : a00546.IsHomogeneous 18 := by
  unfold a00546
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00544.pow 1)))

@[irreducible]
def a00547 : Poly := (C ((-7 : ℂ) / (3 : ℂ)) * a00546 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00543 ^ 1)
theorem ha00547 : a00547.IsHomogeneous 18 := by
  unfold a00547
  exact (((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (3 : ℂ))).mul (ha00546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00543.pow 1)))

@[irreducible]
def a00548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00168 ^ 1)
theorem ha00548 : a00548.IsHomogeneous 24 := by
  unfold a00548
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a00549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00548 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00539 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00540 ^ 1)
theorem ha00549 : a00549.IsHomogeneous 24 := by
  unfold a00549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00548.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00539.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00540.pow 1)))

@[irreducible]
def a00550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00538 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00549 ^ 1)
theorem ha00550 : a00550.IsHomogeneous 24 := by
  unfold a00550
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00549.pow 1)))

@[irreducible]
def a00551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00133 ^ 1)
theorem ha00551 : a00551.IsHomogeneous 18 := by
  unfold a00551
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00032 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00171 ^ 1)
theorem ha00552 : a00552.IsHomogeneous 18 := by
  unfold a00552
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a00553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1)
theorem ha00553 : a00553.IsHomogeneous 6 := by
  unfold a00553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00510 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha00554 : a00554.IsHomogeneous 12 := by
  unfold a00554
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00510.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00553 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00554 ^ 1)
theorem ha00555 : a00555.IsHomogeneous 12 := by
  unfold a00555
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00554.pow 1)))

@[irreducible]
def a00556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00171 ^ 1)
theorem ha00556 : a00556.IsHomogeneous 24 := by
  unfold a00556
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a00557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00556 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00551 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00552 ^ 1)
theorem ha00557 : a00557.IsHomogeneous 24 := by
  unfold a00557
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00556.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00551.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00552.pow 1)))

@[irreducible]
def a00558 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00557 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00534 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00550 ^ 1)
theorem ha00558 : a00558.IsHomogeneous 37 := by
  unfold a00558
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00534.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00550.pow 1)))

@[irreducible]
def a00559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00161 ^ 1)
theorem ha00559 : a00559.IsHomogeneous 18 := by
  unfold a00559
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00161.pow 1)))

@[irreducible]
def a00560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00161 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00528 ^ 1)
theorem ha00560 : a00560.IsHomogeneous 18 := by
  unfold a00560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00528.pow 1)))

@[irreducible]
def a00561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00559 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00560 ^ 1)
theorem ha00561 : a00561.IsHomogeneous 18 := by
  unfold a00561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00560.pow 1)))

@[irreducible]
def a00562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00040 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00179 ^ 1)
theorem ha00562 : a00562.IsHomogeneous 24 := by
  unfold a00562
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00040.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00179.pow 1)))

@[irreducible]
def a00563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha00563 : a00563.IsHomogeneous 12 := by
  unfold a00563
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1)
theorem ha00564 : a00564.IsHomogeneous 24 := by
  unfold a00564
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1)
theorem ha00565 : a00565.IsHomogeneous 18 := by
  unfold a00565
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a00566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00564 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00563 ^ 1)
theorem ha00566 : a00566.IsHomogeneous 24 := by
  unfold a00566
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00564.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00563.pow 1)))

@[irreducible]
def a00567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha00567 : a00567.IsHomogeneous 12 := by
  unfold a00567
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a00568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00510 ^ 1)
theorem ha00568 : a00568.IsHomogeneous 18 := by
  unfold a00568
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a00569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00156 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00324 ^ 1)
theorem ha00569 : a00569.IsHomogeneous 12 := by
  unfold a00569
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00568 ^ 1)
theorem ha00570 : a00570.IsHomogeneous 18 := by
  unfold a00570
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00568.pow 1)))

@[irreducible]
def a00571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00570 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00176 ^ 1)
theorem ha00571 : a00571.IsHomogeneous 24 := by
  unfold a00571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00570.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00176.pow 1)))

@[irreducible]
def a00572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00571 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00567 ^ 1)
theorem ha00572 : a00572.IsHomogeneous 24 := by
  unfold a00572
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00571.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00567.pow 1)))

@[irreducible]
def a00573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00510 ^ 1)
theorem ha00573 : a00573.IsHomogeneous 18 := by
  unfold a00573
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a00574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00130 ^ 2)
theorem ha00574 : a00574.IsHomogeneous 12 := by
  unfold a00574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00130.pow 2)))

@[irreducible]
def a00575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a00156 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00574 ^ 1)
theorem ha00575 : a00575.IsHomogeneous 18 := by
  unfold a00575
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a00576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00573 ^ 1)
theorem ha00576 : a00576.IsHomogeneous 24 := by
  unfold a00576
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00575.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00573.pow 1)))

@[irreducible]
def a00577 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00566 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00576 ^ 1)
theorem ha00577 : a00577.IsHomogeneous 24 := by
  unfold a00577
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00566.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00576.pow 1)))

@[irreducible]
def a00578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1)
theorem ha00578 : a00578.IsHomogeneous 24 := by
  unfold a00578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)))

@[irreducible]
def a00579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00578 ^ 1)
theorem ha00579 : a00579.IsHomogeneous 24 := by
  unfold a00579
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00578.pow 1)))

@[irreducible]
def a00580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00561 ^ 1) + (C ((1 : ℂ) / (270 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00579 ^ 1)
theorem ha00580 : a00580.IsHomogeneous 39 := by
  unfold a00580
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00561.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (270 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00579.pow 1)))

@[irreducible]
def a00581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00157 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00513 ^ 1)
theorem ha00581 : a00581.IsHomogeneous 42 := by
  unfold a00581
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00157.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00513.pow 1)))

@[irreducible]
def a00582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00157 ^ 1)
theorem ha00582 : a00582.IsHomogeneous 33 := by
  unfold a00582
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00157.pow 1)))

@[irreducible]
def a00583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00582 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00581 ^ 1)
theorem ha00583 : a00583.IsHomogeneous 42 := by
  unfold a00583
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00581.pow 1)))

@[irreducible]
def a00584 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a00583 ^ 1)
theorem ha00584 : a00584.IsHomogeneous 48 := by
  unfold a00584
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00561.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha00583.pow 1)))

@[irreducible]
def a00585 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 2 * a00580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00584 ^ 1)
theorem ha00585 : a00585.IsHomogeneous 48 := by
  unfold a00585
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 2)).mul (ha00580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00584.pow 1)))

@[irreducible]
def a00586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1)
theorem ha00586 : a00586.IsHomogeneous 18 := by
  unfold a00586
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a00587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00037 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00168 ^ 1)
theorem ha00587 : a00587.IsHomogeneous 24 := by
  unfold a00587
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a00588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1)
theorem ha00588 : a00588.IsHomogeneous 24 := by
  unfold a00588
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a00589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00587 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00588 ^ 1)
theorem ha00589 : a00589.IsHomogeneous 24 := by
  unfold a00589
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00587.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00588.pow 1)))

@[irreducible]
def a00590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00522 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00589 ^ 1)
theorem ha00590 : a00590.IsHomogeneous 39 := by
  unfold a00590
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00522.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00589.pow 1)))

@[irreducible]
def a00591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1)
theorem ha00591 : a00591.IsHomogeneous 18 := by
  unfold a00591
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00032 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1)
theorem ha00592 : a00592.IsHomogeneous 24 := by
  unfold a00592
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1)
theorem ha00593 : a00593.IsHomogeneous 24 := by
  unfold a00593
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a00594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00592 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00593 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00591 ^ 1)
theorem ha00594 : a00594.IsHomogeneous 24 := by
  unfold a00594
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00592.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00593.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00591.pow 1)))

@[irreducible]
def a00595 : Poly := (C ((-1 : ℂ) / (270 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a00594 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00585 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 2 * a00590 ^ 1)
theorem ha00595 : a00595.IsHomogeneous 48 := by
  unfold a00595
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (270 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00594.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00585.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 2)).mul (ha00590.pow 1)))

@[irreducible]
def a00596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00040 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00179 ^ 1)
theorem ha00596 : a00596.IsHomogeneous 18 := by
  unfold a00596
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00040.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00179.pow 1)))

@[irreducible]
def a00597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00179 ^ 1)
theorem ha00597 : a00597.IsHomogeneous 24 := by
  unfold a00597
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00179.pow 1)))

@[irreducible]
def a00598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00597 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00596 ^ 1)
theorem ha00598 : a00598.IsHomogeneous 24 := by
  unfold a00598
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00596.pow 1)))

@[irreducible]
def a00599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00161 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00528 ^ 1)
theorem ha00599 : a00599.IsHomogeneous 45 := by
  unfold a00599
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00161.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00528.pow 1)))

@[irreducible]
def a00600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00161 ^ 1)
theorem ha00600 : a00600.IsHomogeneous 39 := by
  unfold a00600
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00161.pow 1)))

@[irreducible]
def a00601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00599 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00600 ^ 1)
theorem ha00601 : a00601.IsHomogeneous 45 := by
  unfold a00601
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00599.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00600.pow 1)))

@[irreducible]
def a00602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00601 ^ 1) + (C ((1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00598 ^ 1)
theorem ha00602 : a00602.IsHomogeneous 52 := by
  unfold a00602
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00601.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00598.pow 1)))

@[irreducible]
def a00603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00530 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00598 ^ 1)
theorem ha00603 : a00603.IsHomogeneous 24 := by
  unfold a00603
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00598.pow 1)))

@[irreducible]
def a00604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00602 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00603 ^ 1)
theorem ha00604 : a00604.IsHomogeneous 52 := by
  unfold a00604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00602.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00603.pow 1)))

@[irreducible]
def a00605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00602 ^ 1)
theorem ha00605 : a00605.IsHomogeneous 52 := by
  unfold a00605
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00602.pow 1)))

@[irreducible]
def a00606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00604 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00605 ^ 1)
theorem ha00606 : a00606.IsHomogeneous 52 := by
  unfold a00606
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00604.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00605.pow 1)))

@[irreducible]
def a00607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00020 ^ 1 * a00042 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1)
theorem ha00607 : a00607.IsHomogeneous 39 := by
  unfold a00607
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00020.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00520 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00042 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a00129 ^ 1)
theorem ha00608 : a00608.IsHomogeneous 42 := by
  unfold a00608
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00129 ^ 1)
theorem ha00609 : a00609.IsHomogeneous 39 := by
  unfold a00609
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00607 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00608 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00609 ^ 1)
theorem ha00610 : a00610.IsHomogeneous 45 := by
  unfold a00610
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00608.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00609.pow 1)))

@[irreducible]
def a00611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00610 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00549 ^ 1)
theorem ha00611 : a00611.IsHomogeneous 52 := by
  unfold a00611
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00610.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00549.pow 1)))

@[irreducible]
def a00612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00611 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00550 ^ 1)
theorem ha00612 : a00612.IsHomogeneous 52 := by
  unfold a00612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00611.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00550.pow 1)))

@[irreducible]
def a00613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00054 ^ 1)
theorem ha00613 : a00613.IsHomogeneous 39 := by
  unfold a00613
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00054.pow 1)))

@[irreducible]
def a00614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00201 ^ 1)
theorem ha00614 : a00614.IsHomogeneous 42 := by
  unfold a00614
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha00615 : a00615.IsHomogeneous 24 := by
  unfold a00615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a00616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha00616 : a00616.IsHomogeneous 27 := by
  unfold a00616
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a00617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00616 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00615 ^ 1)
theorem ha00617 : a00617.IsHomogeneous 27 := by
  unfold a00617
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00616.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00615.pow 1)))

@[irreducible]
def a00618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha00618 : a00618.IsHomogeneous 12 := by
  unfold a00618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a00619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00133 ^ 1)
theorem ha00619 : a00619.IsHomogeneous 12 := by
  unfold a00619
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00618 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00619 ^ 1)
theorem ha00620 : a00620.IsHomogeneous 12 := by
  unfold a00620
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00619.pow 1)))

@[irreducible]
def a00621 : Poly := (C ((-1 : ℂ) / (810 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00617 ^ 1)
theorem ha00621 : a00621.IsHomogeneous 27 := by
  unfold a00621
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (810 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00617.pow 1)))

@[irreducible]
def a00622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00621 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00201 ^ 1)
theorem ha00622 : a00622.IsHomogeneous 39 := by
  unfold a00622
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00613 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00614 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00622 ^ 1)
theorem ha00623 : a00623.IsHomogeneous 45 := by
  unfold a00623
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00613.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00614.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00622.pow 1)))

@[irreducible]
def a00624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00623 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00538 ^ 1)
theorem ha00624 : a00624.IsHomogeneous 52 := by
  unfold a00624
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00623.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00538.pow 1)))

@[irreducible]
def a00625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00624 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00550 ^ 1)
theorem ha00625 : a00625.IsHomogeneous 52 := by
  unfold a00625
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00624.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00550.pow 1)))

@[irreducible]
def a00626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00625 ^ 1)
theorem ha00626 : a00626.IsHomogeneous 52 := by
  unfold a00626
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00612.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00625.pow 1)))

@[irreducible]
def a00627 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00133 ^ 1)
theorem ha00627 : a00627.IsHomogeneous 24 := by
  unfold a00627
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00628 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1)
theorem ha00628 : a00628.IsHomogeneous 24 := by
  unfold a00628
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1)
theorem ha00629 : a00629.IsHomogeneous 6 := by
  unfold a00629
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)))

@[irreducible]
def a00630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00324 ^ 1)
theorem ha00630 : a00630.IsHomogeneous 12 := by
  unfold a00630
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00629 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00630 ^ 1)
theorem ha00631 : a00631.IsHomogeneous 12 := by
  unfold a00631
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00630.pow 1)))

@[irreducible]
def a00632 : Poly := (C ((-5 : ℂ) / (28 : ℂ)) * a00631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1)
theorem ha00632 : a00632.IsHomogeneous 12 := by
  unfold a00632
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (28 : ℂ))).mul (ha00631.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)))

@[irreducible]
def a00633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00632 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00207 ^ 1)
theorem ha00633 : a00633.IsHomogeneous 24 := by
  unfold a00633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a00634 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00627 ^ 1) + (C ((15 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00628 ^ 1)
theorem ha00634 : a00634.IsHomogeneous 30 := by
  unfold a00634
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00633.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00627.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00628.pow 1)))

@[irreducible]
def a00635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00557 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00634 ^ 1)
theorem ha00635 : a00635.IsHomogeneous 43 := by
  unfold a00635
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00557.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00634.pow 1)))

@[irreducible]
def a00636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00635 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00557 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00634 ^ 1)
theorem ha00636 : a00636.IsHomogeneous 43 := by
  unfold a00636
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00635.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00557.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00634.pow 1)))

@[irreducible]
def a00637 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00626 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00606 ^ 1) + (C ((1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a00636 ^ 1)
theorem ha00637 : a00637.IsHomogeneous 52 := by
  unfold a00637
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00606.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00636.pow 1)))

@[irreducible]
def a00638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00179 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a00317 ^ 1)
theorem ha00638 : a00638.IsHomogeneous 39 := by
  unfold a00638
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00179.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a00639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00577 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00179 ^ 1)
theorem ha00639 : a00639.IsHomogeneous 48 := by
  unfold a00639
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00577.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00179.pow 1)))

@[irreducible]
def a00640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00639 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00638 ^ 1)
theorem ha00640 : a00640.IsHomogeneous 48 := by
  unfold a00640
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00639.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00638.pow 1)))

@[irreducible]
def a00641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00561 ^ 1) + (C ((4 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00640 ^ 1)
theorem ha00641 : a00641.IsHomogeneous 53 := by
  unfold a00641
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00561.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00640.pow 1)))

@[irreducible]
def a00642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00641 ^ 1) + (C ((4 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00640 ^ 1)
theorem ha00642 : a00642.IsHomogeneous 53 := by
  unfold a00642
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00641.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00640.pow 1)))

@[irreducible]
def a00643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00218 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00064 ^ 1 * a00506 ^ 1)
theorem ha00643 : a00643.IsHomogeneous 48 := by
  unfold a00643
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00218.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00064.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a00644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1)
theorem ha00644 : a00644.IsHomogeneous 30 := by
  unfold a00644
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00042 ^ 1)
theorem ha00645 : a00645.IsHomogeneous 33 := by
  unfold a00645
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00129 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha00646 : a00646.IsHomogeneous 33 := by
  unfold a00646
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00645 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00646 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 3 * a00644 ^ 1)
theorem ha00647 : a00647.IsHomogeneous 33 := by
  unfold a00647
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00646.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 3)).mul (ha00644.pow 1)))

@[irreducible]
def a00648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00032 ^ 1)
theorem ha00648 : a00648.IsHomogeneous 6 := by
  unfold a00648
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)))

@[irreducible]
def a00649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a00133 ^ 2)
theorem ha00649 : a00649.IsHomogeneous 12 := by
  unfold a00649
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha00133.pow 2)))

@[irreducible]
def a00650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00649 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00133 ^ 1)
theorem ha00650 : a00650.IsHomogeneous 18 := by
  unfold a00650
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00649.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00650 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00648 ^ 1)
theorem ha00651 : a00651.IsHomogeneous 18 := by
  unfold a00651
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00650.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00648.pow 1)))

@[irreducible]
def a00652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (8 : ℂ)) * a00025 ^ 1 * a00324 ^ 1)
theorem ha00652 : a00652.IsHomogeneous 12 := by
  unfold a00652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (8 : ℂ))).mul (ha00025.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00574 ^ 1)
theorem ha00653 : a00653.IsHomogeneous 18 := by
  unfold a00653
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a00654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00653 ^ 1)
theorem ha00654 : a00654.IsHomogeneous 18 := by
  unfold a00654
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00652.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00653.pow 1)))

@[irreducible]
def a00655 : Poly := (C ((-7 : ℂ) / (972 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00647 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00654 ^ 1)
theorem ha00655 : a00655.IsHomogeneous 33 := by
  unfold a00655
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (972 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00647.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00654.pow 1)))

@[irreducible]
def a00656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00218 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00655 ^ 1)
theorem ha00656 : a00656.IsHomogeneous 42 := by
  unfold a00656
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00218.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a00657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00656 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00643 ^ 1)
theorem ha00657 : a00657.IsHomogeneous 48 := by
  unfold a00657
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00643.pow 1)))

@[irreducible]
def a00658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00561 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00657 ^ 1)
theorem ha00658 : a00658.IsHomogeneous 53 := by
  unfold a00658
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00561.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00657.pow 1)))

@[irreducible]
def a00659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00641 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00658 ^ 1)
theorem ha00659 : a00659.IsHomogeneous 53 := by
  unfold a00659
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00641.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00658.pow 1)))

@[irreducible]
def a00660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00659 ^ 1)
theorem ha00660 : a00660.IsHomogeneous 53 := by
  unfold a00660
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00659.pow 1)))

@[irreducible]
def a00661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00642 ^ 1) + (C ((4 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00640 ^ 1)
theorem ha00661 : a00661.IsHomogeneous 53 := by
  unfold a00661
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00642.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00640.pow 1)))

@[irreducible]
def a00662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00661 ^ 1)
theorem ha00662 : a00662.IsHomogeneous 53 := by
  unfold a00662
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00661.pow 1)))

@[irreducible]
def a00663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00168 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha00663 : a00663.IsHomogeneous 42 := by
  unfold a00663
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00130 ^ 1 * a00168 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00547 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1 * a00168 ^ 1)
theorem ha00664 : a00664.IsHomogeneous 48 := by
  unfold a00664
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00547.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a00665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha00665 : a00665.IsHomogeneous 39 := by
  unfold a00665
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00664 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00665 ^ 1)
theorem ha00666 : a00666.IsHomogeneous 48 := by
  unfold a00666
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00663.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00664.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00665.pow 1)))

@[irreducible]
def a00667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00522 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00666 ^ 1)
theorem ha00667 : a00667.IsHomogeneous 53 := by
  unfold a00667
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00522.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00666.pow 1)))

@[irreducible]
def a00668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00667 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00666 ^ 1)
theorem ha00668 : a00668.IsHomogeneous 53 := by
  unfold a00668
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00667.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00666.pow 1)))

@[irreducible]
def a00669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha00669 : a00669.IsHomogeneous 42 := by
  unfold a00669
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a00201 ^ 1)
theorem ha00670 : a00670.IsHomogeneous 48 := by
  unfold a00670
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha00506.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00621 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha00671 : a00671.IsHomogeneous 39 := by
  unfold a00671
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00670 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00671 ^ 1)
theorem ha00672 : a00672.IsHomogeneous 48 := by
  unfold a00672
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00670.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00671.pow 1)))

@[irreducible]
def a00673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00522 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00672 ^ 1)
theorem ha00673 : a00673.IsHomogeneous 53 := by
  unfold a00673
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00522.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00672.pow 1)))

@[irreducible]
def a00674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00673 ^ 1)
theorem ha00674 : a00674.IsHomogeneous 53 := by
  unfold a00674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00673.pow 1)))

@[irreducible]
def a00675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00674 ^ 1)
theorem ha00675 : a00675.IsHomogeneous 53 := by
  unfold a00675
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00674.pow 1)))

@[irreducible]
def a00676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00673 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00672 ^ 1)
theorem ha00676 : a00676.IsHomogeneous 53 := by
  unfold a00676
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00673.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00672.pow 1)))

@[irreducible]
def a00677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00674 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00676 ^ 1)
theorem ha00677 : a00677.IsHomogeneous 53 := by
  unfold a00677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00674.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00676.pow 1)))

@[irreducible]
def a00678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00675 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00677 ^ 1)
theorem ha00678 : a00678.IsHomogeneous 53 := by
  unfold a00678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00675.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00677.pow 1)))

@[irreducible]
def a00679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00133 ^ 1)
theorem ha00679 : a00679.IsHomogeneous 42 := by
  unfold a00679
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00042 ^ 1 * a00555 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00032 ^ 1 * a00129 ^ 1 * a00171 ^ 1)
theorem ha00680 : a00680.IsHomogeneous 48 := by
  unfold a00680
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha00555.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a00681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00129 ^ 1 * a00171 ^ 1)
theorem ha00681 : a00681.IsHomogeneous 39 := by
  unfold a00681
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a00682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00679 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00680 ^ 1) + (C ((15 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00681 ^ 1)
theorem ha00682 : a00682.IsHomogeneous 48 := by
  unfold a00682
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00680.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00681.pow 1)))

@[irreducible]
def a00683 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00324 ^ 1)
theorem ha00683 : a00683.IsHomogeneous 24 := by
  unfold a00683
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00684 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a00506 ^ 1) + (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a00207 ^ 1)
theorem ha00684 : a00684.IsHomogeneous 30 := by
  unfold a00684
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a00685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00632 ^ 1)
theorem ha00685 : a00685.IsHomogeneous 24 := by
  unfold a00685
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a00686 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00685 ^ 1) + (C ((-12 : ℂ) / (1 : ℂ)) * a00684 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00683 ^ 1)
theorem ha00686 : a00686.IsHomogeneous 30 := by
  unfold a00686
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00685.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00684.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00683.pow 1)))

@[irreducible]
def a00687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00682 ^ 1) + (C ((1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00686 ^ 1)
theorem ha00687 : a00687.IsHomogeneous 48 := by
  unfold a00687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00682.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00686.pow 1)))

@[irreducible]
def a00688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00682 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00687 ^ 1) + (C ((1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00686 ^ 1)
theorem ha00688 : a00688.IsHomogeneous 48 := by
  unfold a00688
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00682.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00687.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00686.pow 1)))

@[irreducible]
def a00689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00687 ^ 1) + (C ((1 : ℂ) / (1134 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00686 ^ 1)
theorem ha00689 : a00689.IsHomogeneous 48 := by
  unfold a00689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00687.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1134 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00686.pow 1)))

@[irreducible]
def a00690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00688 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00689 ^ 1) + (C ((1 : ℂ) / (756 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00686 ^ 1)
theorem ha00690 : a00690.IsHomogeneous 48 := by
  unfold a00690
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00688.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00689.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (756 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00686.pow 1)))

@[irreducible]
def a00691 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00662 ^ 1) + (C ((28 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00690 ^ 1)
theorem ha00691 : a00691.IsHomogeneous 53 := by
  unfold a00691
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00662.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00690.pow 1)))

@[irreducible]
def a00692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00218 ^ 1)
theorem ha00692 : a00692.IsHomogeneous 42 := by
  unfold a00692
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00218.pow 1)))

@[irreducible]
def a00693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00655 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00218 ^ 1)
theorem ha00693 : a00693.IsHomogeneous 39 := by
  unfold a00693
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00218.pow 1)))

@[irreducible]
def a00694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00693 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00692 ^ 1)
theorem ha00694 : a00694.IsHomogeneous 45 := by
  unfold a00694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00693.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00692.pow 1)))

@[irreducible]
def a00695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00601 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00694 ^ 1)
theorem ha00695 : a00695.IsHomogeneous 45 := by
  unfold a00695
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00694.pow 1)))

@[irreducible]
def a00696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00695 ^ 1)
theorem ha00696 : a00696.IsHomogeneous 45 := by
  unfold a00696
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00695.pow 1)))

@[irreducible]
def a00697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00696 ^ 1)
theorem ha00697 : a00697.IsHomogeneous 45 := by
  unfold a00697
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00696.pow 1)))

@[irreducible]
def a00698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00694 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00695 ^ 1)
theorem ha00698 : a00698.IsHomogeneous 45 := by
  unfold a00698
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00695.pow 1)))

@[irreducible]
def a00699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00696 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00698 ^ 1)
theorem ha00699 : a00699.IsHomogeneous 45 := by
  unfold a00699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00696.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00698.pow 1)))

@[irreducible]
def a00700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00699 ^ 1)
theorem ha00700 : a00700.IsHomogeneous 45 := by
  unfold a00700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00699.pow 1)))

@[irreducible]
def a00701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00697 ^ 1)
theorem ha00701 : a00701.IsHomogeneous 45 := by
  unfold a00701
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00697.pow 1)))

@[irreducible]
def a00702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00700 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00701 ^ 1)
theorem ha00702 : a00702.IsHomogeneous 45 := by
  unfold a00702
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00700.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00701.pow 1)))

@[irreducible]
def a00703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00623 ^ 1)
theorem ha00703 : a00703.IsHomogeneous 45 := by
  unfold a00703
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00623.pow 1)))

@[irreducible]
def a00704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00703 ^ 1)
theorem ha00704 : a00704.IsHomogeneous 45 := by
  unfold a00704
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00703.pow 1)))

@[irreducible]
def a00705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00704 ^ 1)
theorem ha00705 : a00705.IsHomogeneous 45 := by
  unfold a00705
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00704.pow 1)))

@[irreducible]
def a00706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00703 ^ 1)
theorem ha00706 : a00706.IsHomogeneous 45 := by
  unfold a00706
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00703.pow 1)))

@[irreducible]
def a00707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00704 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00706 ^ 1)
theorem ha00707 : a00707.IsHomogeneous 45 := by
  unfold a00707
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00704.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00706.pow 1)))

@[irreducible]
def a00708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00707 ^ 1)
theorem ha00708 : a00708.IsHomogeneous 45 := by
  unfold a00708
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00705.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00707.pow 1)))

@[irreducible]
def a00709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00706 ^ 1)
theorem ha00709 : a00709.IsHomogeneous 45 := by
  unfold a00709
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00706.pow 1)))

@[irreducible]
def a00710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00709 ^ 1)
theorem ha00710 : a00710.IsHomogeneous 45 := by
  unfold a00710
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00709.pow 1)))

@[irreducible]
def a00711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00708 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00710 ^ 1)
theorem ha00711 : a00711.IsHomogeneous 45 := by
  unfold a00711
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00708.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00710.pow 1)))

@[irreducible]
def a00712 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00711 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00702 ^ 1) + (C ((35 : ℂ) / (1458 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00634 ^ 1)
theorem ha00712 : a00712.IsHomogeneous 45 := by
  unfold a00712
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00711.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00702.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00634.pow 1)))

@[irreducible]
def a00713 : Poly := (C ((-27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00003 ^ 2 * a00012 ^ 5 * a00014 ^ 4 * a00523 ^ 1) + (C ((-3 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a00014 ^ 2 * a00595 ^ 1) + (C ((-1 : ℂ) / (1600 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00003 ^ 2 * a00004 ^ 6 * a00005 ^ 6 * a00014 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 3 * a00558 ^ 1) + (C ((1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00003 ^ 1 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a00691 ^ 1)
theorem ha00713 : a00713.IsHomogeneous 90 := by
  unfold a00713
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 5)).mul (ha00014.pow 4)).mul (ha00523.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00595.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1600 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha00014.pow 1)).mul (ha00712.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00558.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00003.pow 1)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a00714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00713 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00261 ^ 2)
theorem ha00714 : a00714.IsHomogeneous 170 := by
  unfold a00714
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a00715 : Poly := (C ((-5 : ℂ) / (128 : ℂ)) * a00714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 2)
theorem ha00715 : a00715.IsHomogeneous 170 := by
  unfold a00715
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (128 : ℂ))).mul (ha00714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a00716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00715 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a00295 ^ 1)
theorem ha00716 : a00716.IsHomogeneous 553 := by
  unfold a00716
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00715.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha00295.pow 1)))

@[irreducible]
def a00717 : Poly := (C ((-1 : ℂ) / (270 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00506 ^ 1) + (C ((-1 : ℂ) / (699840 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 3 * a00315 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00102 ^ 1 * a00316 ^ 1)
theorem ha00717 : a00717.IsHomogeneous 40 := by
  unfold a00717
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (270 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00506.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (699840 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00315.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00102.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a00718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00262 ^ 1)
theorem ha00718 : a00718.IsHomogeneous 46 := by
  unfold a00718
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00103 ^ 1)
theorem ha00719 : a00719.IsHomogeneous 46 := by
  unfold a00719
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)))

@[irreducible]
def a00720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00718 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00719 ^ 1)
theorem ha00720 : a00720.IsHomogeneous 46 := by
  unfold a00720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00719.pow 1)))

@[irreducible]
def a00721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 5 * a00012 ^ 2 * a00510 ^ 1) + (C ((7 : ℂ) / (216 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00004 ^ 4 * a00005 ^ 1 * a00323 ^ 1) + (C ((7 : ℂ) / (432 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00004 ^ 4 * a00005 ^ 1 * a00321 ^ 1)
theorem ha00721 : a00721.IsHomogeneous 24 := by
  unfold a00721
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 5)).mul (ha00012.pow 2)).mul (ha00510.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (216 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00323.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (432 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00321.pow 1)))

@[irreducible]
def a00722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00104 ^ 1 * a00721 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00264 ^ 2)
theorem ha00722 : a00722.IsHomogeneous 50 := by
  unfold a00722
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00104.pow 1)).mul (ha00721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00264.pow 2)))

@[irreducible]
def a00723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00722 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00720 ^ 1)
theorem ha00723 : a00723.IsHomogeneous 54 := by
  unfold a00723
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00722.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00720.pow 1)))

@[irreducible]
def a00724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 2) + (C ((1 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a00723 ^ 1)
theorem ha00724 : a00724.IsHomogeneous 110 := by
  unfold a00724
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha00723.pow 1)))

@[irreducible]
def a00725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00117 ^ 1 * a00724 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00265 ^ 1 * a00270 ^ 1)
theorem ha00725 : a00725.IsHomogeneous 134 := by
  unfold a00725
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00117.pow 1)).mul (ha00724.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00270.pow 1)))

@[irreducible]
def a00726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00108 ^ 1) + (C ((2 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1)
theorem ha00726 : a00726.IsHomogeneous 22 := by
  unfold a00726
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00108.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00266 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00726 ^ 1)
theorem ha00727 : a00727.IsHomogeneous 22 := by
  unfold a00727
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00726.pow 1)))

@[irreducible]
def a00728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00727 ^ 1)
theorem ha00728 : a00728.IsHomogeneous 22 := by
  unfold a00728
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00727.pow 1)))

@[irreducible]
def a00729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00005 ^ 4 * a00012 ^ 2) + (C ((1 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1) + (C ((1 : ℂ) / (19440 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00012 ^ 1)
theorem ha00729 : a00729.IsHomogeneous 20 := by
  unfold a00729
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (19440 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00268 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00729 ^ 1)
theorem ha00730 : a00730.IsHomogeneous 20 := by
  unfold a00730
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00729.pow 1)))

@[irreducible]
def a00731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00730 ^ 1)
theorem ha00731 : a00731.IsHomogeneous 20 := by
  unfold a00731
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00730.pow 1)))

@[irreducible]
def a00732 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00728 ^ 1)
theorem ha00732 : a00732.IsHomogeneous 22 := by
  unfold a00732
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00728.pow 1)))

@[irreducible]
def a00733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a00270 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a00732 ^ 1)
theorem ha00733 : a00733.IsHomogeneous 79 := by
  unfold a00733
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha00270.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha00732.pow 1)))

@[irreducible]
def a00734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00725 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00733 ^ 1)
theorem ha00734 : a00734.IsHomogeneous 134 := by
  unfold a00734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00733.pow 1)))

@[irreducible]
def a00735 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00734 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00271 ^ 1 * a00286 ^ 1)
theorem ha00735 : a00735.IsHomogeneous 279 := by
  unfold a00735
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00734.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00271.pow 1)).mul (ha00286.pow 1)))

@[irreducible]
def a00736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00123 ^ 1 * a00262 ^ 1)
theorem ha00736 : a00736.IsHomogeneous 139 := by
  unfold a00736
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00123.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 2) + (C ((5 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a00717 ^ 1)
theorem ha00737 : a00737.IsHomogeneous 82 := by
  unfold a00737
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a00738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00123 ^ 1 * a00737 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00123 ^ 1 * a00262 ^ 1)
theorem ha00738 : a00738.IsHomogeneous 185 := by
  unfold a00738
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00737.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1)
theorem ha00739 : a00739.IsHomogeneous 48 := by
  unfold a00739
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00262 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00262 ^ 1)
theorem ha00740 : a00740.IsHomogeneous 52 := by
  unfold a00740
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00262.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00009 ^ 1 * a00103 ^ 1)
theorem ha00741 : a00741.IsHomogeneous 52 := by
  unfold a00741
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00009.pow 1)).mul (ha00103.pow 1)))

@[irreducible]
def a00742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00740 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00739 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00741 ^ 1)
theorem ha00742 : a00742.IsHomogeneous 52 := by
  unfold a00742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00740.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00739.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00741.pow 1)))

@[irreducible]
def a00743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00104 ^ 1)
theorem ha00743 : a00743.IsHomogeneous 25 := by
  unfold a00743
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00104.pow 1)))

@[irreducible]
def a00744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00104 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a00722 ^ 1)
theorem ha00744 : a00744.IsHomogeneous 56 := by
  unfold a00744
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha00722.pow 1)))

@[irreducible]
def a00745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00104 ^ 1 * a00743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00744 ^ 1)
theorem ha00745 : a00745.IsHomogeneous 56 := by
  unfold a00745
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)).mul (ha00743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00744.pow 1)))

@[irreducible]
def a00746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00721 ^ 1)
theorem ha00746 : a00746.IsHomogeneous 31 := by
  unfold a00746
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a00747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a00264 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00104 ^ 1 * a00574 ^ 1)
theorem ha00747 : a00747.IsHomogeneous 37 := by
  unfold a00747
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00104.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a00748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00746 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00747 ^ 1)
theorem ha00748 : a00748.IsHomogeneous 37 := by
  unfold a00748
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00747.pow 1)))

@[irreducible]
def a00749 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 2 * a00748 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00745 ^ 1) + (C ((5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00742 ^ 1)
theorem ha00749 : a00749.IsHomogeneous 60 := by
  unfold a00749
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00748.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00745.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00742.pow 1)))

@[irreducible]
def a00750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00275 ^ 1 * a00276 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00120 ^ 1 * a00749 ^ 1)
theorem ha00750 : a00750.IsHomogeneous 91 := by
  unfold a00750
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00275.pow 1)).mul (ha00276.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00120.pow 1)).mul (ha00749.pow 1)))

@[irreducible]
def a00751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00119 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (3240 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00315 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00012 ^ 2 * a00506 ^ 1)
theorem ha00751 : a00751.IsHomogeneous 29 := by
  unfold a00751
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00119.pow 1)).mul (ha00316.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3240 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00315.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha00506.pow 1)))

@[irreducible]
def a00752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1 * a00751 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00275 ^ 1 * a00276 ^ 1)
theorem ha00752 : a00752.IsHomogeneous 90 := by
  unfold a00752
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).mul (ha00751.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00275.pow 1)).mul (ha00276.pow 1)))

@[irreducible]
def a00753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00752 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00750 ^ 1)
theorem ha00753 : a00753.IsHomogeneous 91 := by
  unfold a00753
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00752.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00750.pow 1)))

@[irreducible]
def a00754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a00280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a00262 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a00121 ^ 1)
theorem ha00754 : a00754.IsHomogeneous 94 := by
  unfold a00754
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha00280.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha00121.pow 1)))

@[irreducible]
def a00755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00121 ^ 1 * a00717 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a00262 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a00280 ^ 1)
theorem ha00755 : a00755.IsHomogeneous 94 := by
  unfold a00755
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a00756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha00756 : a00756.IsHomogeneous 42 := by
  unfold a00756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a00757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00262 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a00717 ^ 1)
theorem ha00757 : a00757.IsHomogeneous 46 := by
  unfold a00757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a00758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00756 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00757 ^ 1)
theorem ha00758 : a00758.IsHomogeneous 46 := by
  unfold a00758
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00757.pow 1)))

@[irreducible]
def a00759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00104 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00264 ^ 1)
theorem ha00759 : a00759.IsHomogeneous 31 := by
  unfold a00759
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00264.pow 1)))

@[irreducible]
def a00760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00721 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00264 ^ 1)
theorem ha00760 : a00760.IsHomogeneous 31 := by
  unfold a00760
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00264.pow 1)))

@[irreducible]
def a00761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00759 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00760 ^ 1)
theorem ha00761 : a00761.IsHomogeneous 31 := by
  unfold a00761
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00759.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00760.pow 1)))

@[irreducible]
def a00762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00758 ^ 1) + (C ((7 : ℂ) / (540 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00761 ^ 1)
theorem ha00762 : a00762.IsHomogeneous 46 := by
  unfold a00762
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00758.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (540 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00761.pow 1)))

@[irreducible]
def a00763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1 * a00762 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a00280 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a00280 ^ 1)
theorem ha00763 : a00763.IsHomogeneous 94 := by
  unfold a00763
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha00280.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a00764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00754 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00755 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00763 ^ 1)
theorem ha00764 : a00764.IsHomogeneous 94 := by
  unfold a00764
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00754.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00755.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00763.pow 1)))

@[irreducible]
def a00765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00122 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a00262 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00262 ^ 1 * a00283 ^ 1)
theorem ha00765 : a00765.IsHomogeneous 77 := by
  unfold a00765
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha00262.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a00766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00264 ^ 1)
theorem ha00766 : a00766.IsHomogeneous 25 := by
  unfold a00766
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00264.pow 1)))

@[irreducible]
def a00767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00264 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a00721 ^ 1)
theorem ha00767 : a00767.IsHomogeneous 30 := by
  unfold a00767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a00768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00766 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00767 ^ 1)
theorem ha00768 : a00768.IsHomogeneous 30 := by
  unfold a00768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00767.pow 1)))

@[irreducible]
def a00769 : Poly := (C ((-7 : ℂ) / (270 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00004 ^ 4 * a00005 ^ 1 * a00574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00768 ^ 1)
theorem ha00769 : a00769.IsHomogeneous 30 := by
  unfold a00769
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (270 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00768.pow 1)))

@[irreducible]
def a00770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a00283 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00103 ^ 1 * a00769 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00262 ^ 1 * a00283 ^ 1)
theorem ha00770 : a00770.IsHomogeneous 79 := by
  unfold a00770
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha00283.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha00769.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a00771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a00283 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 2 * a00122 ^ 1 * a00133 ^ 1 * a00262 ^ 1)
theorem ha00771 : a00771.IsHomogeneous 79 := by
  unfold a00771
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha00283.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 2)).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00770 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00771 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00765 ^ 1)
theorem ha00772 : a00772.IsHomogeneous 79 := by
  unfold a00772
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00771.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00765.pow 1)))

@[irreducible]
def a00773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00753 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 2 * a00772 ^ 1) + (C ((648 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00764 ^ 1)
theorem ha00773 : a00773.IsHomogeneous 96 := by
  unfold a00773
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00753.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00772.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((648 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00764.pow 1)))

@[irreducible]
def a00774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00773 ^ 1)
theorem ha00774 : a00774.IsHomogeneous 144 := by
  unfold a00774
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00773.pow 1)))

@[irreducible]
def a00775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00774 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00736 ^ 1)
theorem ha00775 : a00775.IsHomogeneous 186 := by
  unfold a00775
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00738.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00774.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00736.pow 1)))

@[irreducible]
def a00776 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 2)
theorem ha00776 : a00776.IsHomogeneous 290 := by
  unfold a00776
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 2)))

@[irreducible]
def a00777 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1 * a00286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a00776 ^ 1)
theorem ha00777 : a00777.IsHomogeneous 369 := by
  unfold a00777
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).mul (ha00286.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00776.pow 1)))

@[irreducible]
def a00778 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00777 ^ 1)
theorem ha00778 : a00778.IsHomogeneous 424 := by
  unfold a00778
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00735.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00777.pow 1)))

@[irreducible]
def a00779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00778 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00287 ^ 1 * a00291 ^ 1)
theorem ha00779 : a00779.IsHomogeneous 484 := by
  unfold a00779
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00778.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00287.pow 1)).mul (ha00291.pow 1)))

@[irreducible]
def a00780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00289 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00265 ^ 1)
theorem ha00780 : a00780.IsHomogeneous 121 := by
  unfold a00780
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00289.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)))

@[irreducible]
def a00781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00131 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00781 : a00781.IsHomogeneous 6 := by
  unfold a00781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00131.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha00782 : a00782.IsHomogeneous 6 := by
  unfold a00782
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00783 : Poly := (C ((-1 : ℂ) / (77760 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 4 * a00012 ^ 4) + (C ((-1 : ℂ) / (116640 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 3 * a00102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00102 ^ 2 * a00782 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 1 * a00005 ^ 3 * a00012 ^ 6 * a00781 ^ 1) + (C ((7 : ℂ) / (360 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1 * a00321 ^ 1)
theorem ha00783 : a00783.IsHomogeneous 58 := by
  unfold a00783
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (77760 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 4)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (116640 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00102.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00102.pow 2)).mul (ha00782.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 6)).mul (ha00781.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (360 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1)).mul (ha00321.pow 1)))

@[irreducible]
def a00784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00289 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00289 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00783 ^ 1)
theorem ha00784 : a00784.IsHomogeneous 119 := by
  unfold a00784
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00289.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a00785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a00723 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00265 ^ 2)
theorem ha00785 : a00785.IsHomogeneous 110 := by
  unfold a00785
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha00723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00265.pow 2)))

@[irreducible]
def a00786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00785 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00124 ^ 1 * a00265 ^ 1)
theorem ha00786 : a00786.IsHomogeneous 176 := by
  unfold a00786
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)))

@[irreducible]
def a00787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00784 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00786 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00780 ^ 1)
theorem ha00787 : a00787.IsHomogeneous 182 := by
  unfold a00787
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00784.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00786.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00780.pow 1)))

@[irreducible]
def a00788 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00285 ^ 1 * a00290 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00787 ^ 1)
theorem ha00788 : a00788.IsHomogeneous 279 := by
  unfold a00788
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00285.pow 1)).mul (ha00290.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00787.pow 1)))

@[irreducible]
def a00789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00773 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 2)
theorem ha00789 : a00789.IsHomogeneous 194 := by
  unfold a00789
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a00790 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 2)
theorem ha00790 : a00790.IsHomogeneous 194 := by
  unfold a00790
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a00791 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a00790 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00285 ^ 1 * a00290 ^ 1)
theorem ha00791 : a00791.IsHomogeneous 315 := by
  unfold a00791
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00790.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha00290.pow 1)))

@[irreducible]
def a00792 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00791 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00788 ^ 1)
theorem ha00792 : a00792.IsHomogeneous 376 := by
  unfold a00792
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00791.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00788.pow 1)))

@[irreducible]
def a00793 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 2)
theorem ha00793 : a00793.IsHomogeneous 436 := by
  unfold a00793
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 2)))

@[irreducible]
def a00794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1 * a00291 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a00793 ^ 1)
theorem ha00794 : a00794.IsHomogeneous 502 := by
  unfold a00794
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).mul (ha00291.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha00793.pow 1)))

@[irreducible]
def a00795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00779 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00794 ^ 1)
theorem ha00795 : a00795.IsHomogeneous 544 := by
  unfold a00795
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00794.pow 1)))

@[irreducible]
def a00796 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a00294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a00795 ^ 1)
theorem ha00796 : a00796.IsHomogeneous 649 := by
  unfold a00796
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha00294.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha00795.pow 1)))

@[irreducible]
def a00797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00125 ^ 1 * a00712 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00260 ^ 1 * a00293 ^ 1)
theorem ha00797 : a00797.IsHomogeneous 117 := by
  unfold a00797
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00125.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00260.pow 1)).mul (ha00293.pow 1)))

@[irreducible]
def a00798 : Poly := (C ((-9 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00595 ^ 1) + (C ((-1 : ℂ) / (320 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00558 ^ 1) + (C ((1 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00691 ^ 1)
theorem ha00798 : a00798.IsHomogeneous 80 := by
  unfold a00798
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00595.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (320 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00712.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00558.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a00799 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00293 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00798 ^ 1)
theorem ha00799 : a00799.IsHomogeneous 117 := by
  unfold a00799
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00293.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a00800 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00797 ^ 1)
theorem ha00800 : a00800.IsHomogeneous 117 := by
  unfold a00800
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00797.pow 1)))

@[irreducible]
def a00801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a00294 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00800 ^ 1)
theorem ha00801 : a00801.IsHomogeneous 395 := by
  unfold a00801
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha00294.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00800.pow 1)))

@[irreducible]
def a00802 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00796 ^ 1)
theorem ha00802 : a00802.IsHomogeneous 649 := by
  unfold a00802
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00801.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00796.pow 1)))

@[irreducible]
def a00803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a00295 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00802 ^ 1)
theorem ha00803 : a00803.IsHomogeneous 728 := by
  unfold a00803
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha00295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00802.pow 1)))

@[irreducible]
def a00804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00716 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00803 ^ 1)
theorem ha00804 : a00804.IsHomogeneous 807 := by
  unfold a00804
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00803.pow 1)))

@[irreducible]
def a00805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00306 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00804 ^ 1)
theorem ha00805 : a00805.IsHomogeneous 915 := by
  unfold a00805
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00306.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00804.pow 1)))

@[irreducible]
def a00806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1)
theorem ha00806 : a00806.IsHomogeneous 27 := by
  unfold a00806
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)))

@[irreducible]
def a00807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1)
theorem ha00807 : a00807.IsHomogeneous 27 := by
  unfold a00807
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00806 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00807 ^ 1)
theorem ha00808 : a00808.IsHomogeneous 27 := by
  unfold a00808
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00807.pow 1)))

@[irreducible]
def a00809 : Poly := (C ((-7 : ℂ) / (3888 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00808 ^ 1)
theorem ha00809 : a00809.IsHomogeneous 27 := by
  unfold a00809
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (3888 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00808.pow 1)))

@[irreducible]
def a00810 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00303 ^ 1)
theorem ha00810 : a00810.IsHomogeneous 144 := by
  unfold a00810
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00303.pow 1)))

@[irreducible]
def a00811 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00155 ^ 1)
theorem ha00811 : a00811.IsHomogeneous 114 := by
  unfold a00811
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00302.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00782 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha00812 : a00812.IsHomogeneous 15 := by
  unfold a00812
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00782.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a00813 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a00301 ^ 1)
theorem ha00813 : a00813.IsHomogeneous 111 := by
  unfold a00813
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha00301.pow 1)))

@[irreducible]
def a00814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00126 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a00300 ^ 1)
theorem ha00814 : a00814.IsHomogeneous 102 := by
  unfold a00814
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a00815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha00815 : a00815.IsHomogeneous 51 := by
  unfold a00815
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00809 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha00816 : a00816.IsHomogeneous 51 := by
  unfold a00816
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00815 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00816 ^ 1)
theorem ha00817 : a00817.IsHomogeneous 51 := by
  unfold a00817
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00816.pow 1)))

@[irreducible]
def a00818 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00817 ^ 1)
theorem ha00818 : a00818.IsHomogeneous 96 := by
  unfold a00818
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00300.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a00819 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00818 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00814 ^ 1)
theorem ha00819 : a00819.IsHomogeneous 102 := by
  unfold a00819
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00818.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00814.pow 1)))

@[irreducible]
def a00820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00301 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00127 ^ 1 * a00819 ^ 1)
theorem ha00820 : a00820.IsHomogeneous 120 := by
  unfold a00820
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00301.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00127.pow 1)).mul (ha00819.pow 1)))

@[irreducible]
def a00821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00813 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00820 ^ 1)
theorem ha00821 : a00821.IsHomogeneous 120 := by
  unfold a00821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00813.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00820.pow 1)))

@[irreducible]
def a00822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00302 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00821 ^ 1)
theorem ha00822 : a00822.IsHomogeneous 120 := by
  unfold a00822
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00302.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00821.pow 1)))

@[irreducible]
def a00823 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00822 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00811 ^ 1)
theorem ha00823 : a00823.IsHomogeneous 120 := by
  unfold a00823
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00822.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00811.pow 1)))

@[irreducible]
def a00824 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00303 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00823 ^ 1)
theorem ha00824 : a00824.IsHomogeneous 150 := by
  unfold a00824
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00303.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00823.pow 1)))

@[irreducible]
def a00825 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00810 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00824 ^ 1)
theorem ha00825 : a00825.IsHomogeneous 150 := by
  unfold a00825
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00824.pow 1)))

@[irreducible]
def a00826 : Poly := (C ((-5 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00304 ^ 1 * a00305 ^ 1)
theorem ha00826 : a00826.IsHomogeneous 210 := by
  unfold a00826
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00825.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00304.pow 1)).mul (ha00305.pow 1)))

@[irreducible]
def a00827 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00260 ^ 1)
theorem ha00827 : a00827.IsHomogeneous 63 := by
  unfold a00827
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a00828 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2)
theorem ha00828 : a00828.IsHomogeneous 84 := by
  unfold a00828
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)))

@[irreducible]
def a00829 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha00829 : a00829.IsHomogeneous 84 := by
  unfold a00829
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a00830 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2)
theorem ha00830 : a00830.IsHomogeneous 84 := by
  unfold a00830
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)))

@[irreducible]
def a00831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00828 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00830 ^ 1)
theorem ha00831 : a00831.IsHomogeneous 84 := by
  unfold a00831
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00830.pow 1)))

@[irreducible]
def a00832 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00129 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00831 ^ 1)
theorem ha00832 : a00832.IsHomogeneous 108 := by
  unfold a00832
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a00833 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00832 ^ 1)
theorem ha00833 : a00833.IsHomogeneous 108 := by
  unfold a00833
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00832.pow 1)))

@[irreducible]
def a00834 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 2)
theorem ha00834 : a00834.IsHomogeneous 132 := by
  unfold a00834
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 2)))

@[irreducible]
def a00835 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1 * a00305 ^ 1)
theorem ha00835 : a00835.IsHomogeneous 180 := by
  unfold a00835
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00834.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)).mul (ha00305.pow 1)))

@[irreducible]
def a00836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00826 ^ 1)
theorem ha00836 : a00836.IsHomogeneous 210 := by
  unfold a00836
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00835.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00826.pow 1)))

@[irreducible]
def a00837 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00296 ^ 1 * a00306 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00836 ^ 1)
theorem ha00837 : a00837.IsHomogeneous 636 := by
  unfold a00837
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00296.pow 1)).mul (ha00306.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a00838 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00837 ^ 1)
theorem ha00838 : a00838.IsHomogeneous 969 := by
  unfold a00838
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00805.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00837.pow 1)))

@[irreducible]
def a00839 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00310 ^ 1)
theorem ha00839 : a00839.IsHomogeneous 891 := by
  unfold a00839
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00310.pow 1)))

@[irreducible]
def a00840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00299 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00126 ^ 1 * a00812 ^ 1)
theorem ha00840 : a00840.IsHomogeneous 45 := by
  unfold a00840
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00126.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a00841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00809 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00298 ^ 2)
theorem ha00841 : a00841.IsHomogeneous 60 := by
  unfold a00841
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00298.pow 2)))

@[irreducible]
def a00842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00298 ^ 1 * a00299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a00841 ^ 1)
theorem ha00842 : a00842.IsHomogeneous 78 := by
  unfold a00842
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha00299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a00843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00842 ^ 1)
theorem ha00843 : a00843.IsHomogeneous 78 := by
  unfold a00843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00840.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00842.pow 1)))

@[irreducible]
def a00844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a00308 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00843 ^ 1)
theorem ha00844 : a00844.IsHomogeneous 84 := by
  unfold a00844
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha00308.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00843.pow 1)))

@[irreducible]
def a00845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00155 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00308 ^ 1)
theorem ha00845 : a00845.IsHomogeneous 54 := by
  unfold a00845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00308.pow 1)))

@[irreducible]
def a00846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a00845 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00844 ^ 1)
theorem ha00846 : a00846.IsHomogeneous 90 := by
  unfold a00846
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha00845.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00844.pow 1)))

@[irreducible]
def a00847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00260 ^ 1 * a00309 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00846 ^ 1)
theorem ha00847 : a00847.IsHomogeneous 126 := by
  unfold a00847
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00260.pow 1)).mul (ha00309.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00846.pow 1)))

@[irreducible]
def a00848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (4 : ℂ)) * a00829 ^ 1)
theorem ha00848 : a00848.IsHomogeneous 84 := by
  unfold a00848
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a00849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00848 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a00309 ^ 1)
theorem ha00849 : a00849.IsHomogeneous 132 := by
  unfold a00849
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00309.pow 1)))

@[irreducible]
def a00850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00849 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00847 ^ 1)
theorem ha00850 : a00850.IsHomogeneous 162 := by
  unfold a00850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00849.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00847.pow 1)))

@[irreducible]
def a00851 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00296 ^ 1 * a00310 ^ 1)
theorem ha00851 : a00851.IsHomogeneous 588 := by
  unfold a00851
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00850.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00296.pow 1)).mul (ha00310.pow 1)))

@[irreducible]
def a00852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00851 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00839 ^ 1)
theorem ha00852 : a00852.IsHomogeneous 921 := by
  unfold a00852
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00851.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00839.pow 1)))

@[irreducible]
def a00853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00838 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a00042 ^ 2 * a00852 ^ 1)
theorem ha00853 : a00853.IsHomogeneous 969 := by
  unfold a00853
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00838.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha00042.pow 2)).mul (ha00852.pow 1)))

@[irreducible]
def a00854 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00312 ^ 1 * a00327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00853 ^ 1)
theorem ha00854 : a00854.IsHomogeneous 1029 := by
  unfold a00854
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00312.pow 1)).mul (ha00327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00853.pow 1)))

@[irreducible]
def a00855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha00855 : a00855.IsHomogeneous 54 := by
  unfold a00855
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha00856 : a00856.IsHomogeneous 51 := by
  unfold a00856
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00809 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00298 ^ 1)
theorem ha00857 : a00857.IsHomogeneous 54 := by
  unfold a00857
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00809.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00855 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00856 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00857 ^ 1)
theorem ha00858 : a00858.IsHomogeneous 54 := by
  unfold a00858
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00855.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00856.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00857.pow 1)))

@[irreducible]
def a00859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00655 ^ 1)
theorem ha00859 : a00859.IsHomogeneous 57 := by
  unfold a00859
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a00860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (24 : ℂ)) * a00017 ^ 1)
theorem ha00860 : a00860.IsHomogeneous 6 := by
  unfold a00860
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00017.pow 1)))

@[irreducible]
def a00861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((2 : ℂ) / (7 : ℂ)) * a00860 ^ 1)
theorem ha00861 : a00861.IsHomogeneous 6 := by
  unfold a00861
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00860.pow 1)))

@[irreducible]
def a00862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((3 : ℂ) / (8 : ℂ)) * a00861 ^ 1)
theorem ha00862 : a00862.IsHomogeneous 6 := by
  unfold a00862
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00861.pow 1)))

@[irreducible]
def a00863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1)
theorem ha00863 : a00863.IsHomogeneous 6 := by
  unfold a00863
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)))

@[irreducible]
def a00864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00132 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00863 ^ 1)
theorem ha00864 : a00864.IsHomogeneous 12 := by
  unfold a00864
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00863.pow 1)))

@[irreducible]
def a00865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00862 ^ 1)
theorem ha00865 : a00865.IsHomogeneous 21 := by
  unfold a00865
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00862.pow 1)))

@[irreducible]
def a00866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00218 ^ 1 * a00317 ^ 1)
theorem ha00866 : a00866.IsHomogeneous 57 := by
  unfold a00866
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00218.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a00867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00859 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00866 ^ 1)
theorem ha00867 : a00867.IsHomogeneous 57 := by
  unfold a00867
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00859.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00866.pow 1)))

@[irreducible]
def a00868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a00129 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha00868 : a00868.IsHomogeneous 57 := by
  unfold a00868
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha00129.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00201 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a00201 ^ 1)
theorem ha00869 : a00869.IsHomogeneous 57 := by
  unfold a00869
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00201.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00054 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00201 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00129 ^ 1)
theorem ha00870 : a00870.IsHomogeneous 54 := by
  unfold a00870
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00869 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00870 ^ 1)
theorem ha00871 : a00871.IsHomogeneous 57 := by
  unfold a00871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00869.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00870.pow 1)))

@[irreducible]
def a00872 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00317 ^ 1)
theorem ha00872 : a00872.IsHomogeneous 39 := by
  unfold a00872
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a00873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a00207 ^ 1)
theorem ha00873 : a00873.IsHomogeneous 42 := by
  unfold a00873
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a00874 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a00324 ^ 1)
theorem ha00874 : a00874.IsHomogeneous 42 := by
  unfold a00874
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a00875 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00872 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00873 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00874 ^ 1)
theorem ha00875 : a00875.IsHomogeneous 42 := by
  unfold a00875
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00872.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00873.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00874.pow 1)))

@[irreducible]
def a00876 : Poly := (C ((-7 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00875 ^ 1) + (C ((-2 : ℂ) / (1 : ℂ)) * a00871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00867 ^ 1) + (C ((4 : ℂ) / (27 : ℂ)) * a00003 ^ 3 * a00858 ^ 1)
theorem ha00876 : a00876.IsHomogeneous 57 := by
  unfold a00876
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00871.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00867.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (27 : ℂ))).mul (ha00003.pow 3)).mul (ha00858.pow 1)))

@[irreducible]
def a00877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00326 ^ 1)
theorem ha00877 : a00877.IsHomogeneous 99 := by
  unfold a00877
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00876.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00326.pow 1)))

@[irreducible]
def a00878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha00878 : a00878.IsHomogeneous 84 := by
  unfold a00878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a00879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00878 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00326 ^ 1)
theorem ha00879 : a00879.IsHomogeneous 144 := by
  unfold a00879
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00878.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00326.pow 1)))

@[irreducible]
def a00880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00879 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00877 ^ 1)
theorem ha00880 : a00880.IsHomogeneous 144 := by
  unfold a00880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00879.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00877.pow 1)))

@[irreducible]
def a00881 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 2)
theorem ha00881 : a00881.IsHomogeneous 204 := by
  unfold a00881
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 2)))

@[irreducible]
def a00882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1 * a00327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00881 ^ 1)
theorem ha00882 : a00882.IsHomogeneous 702 := by
  unfold a00882
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).mul (ha00327.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00881.pow 1)))

@[irreducible]
def a00883 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00882 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00854 ^ 1)
theorem ha00883 : a00883.IsHomogeneous 1089 := by
  unfold a00883
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00882.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00854.pow 1)))

@[irreducible]
def a00884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00042 ^ 1)
theorem ha00884 : a00884.IsHomogeneous 36 := by
  unfold a00884
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha00885 : a00885.IsHomogeneous 36 := by
  unfold a00885
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00884 ^ 1) + (C ((10 : ℂ) / (27 : ℂ)) * a00885 ^ 1)
theorem ha00886 : a00886.IsHomogeneous 36 := by
  unfold a00886
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (27 : ℂ))).mul (ha00885.pow 1)))

@[irreducible]
def a00887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00886 ^ 1)
theorem ha00887 : a00887.IsHomogeneous 36 := by
  unfold a00887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00886.pow 1)))

@[irreducible]
def a00888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00887 ^ 1)
theorem ha00888 : a00888.IsHomogeneous 36 := by
  unfold a00888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00887.pow 1)))

@[irreducible]
def a00889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00885 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00886 ^ 1)
theorem ha00889 : a00889.IsHomogeneous 36 := by
  unfold a00889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00886.pow 1)))

@[irreducible]
def a00890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00887 ^ 1) + (C ((10 : ℂ) / (27 : ℂ)) * a00889 ^ 1)
theorem ha00890 : a00890.IsHomogeneous 36 := by
  unfold a00890
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (27 : ℂ))).mul (ha00889.pow 1)))

@[irreducible]
def a00891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00888 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00890 ^ 1)
theorem ha00891 : a00891.IsHomogeneous 36 := by
  unfold a00891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00890.pow 1)))

@[irreducible]
def a00892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00888 ^ 1)
theorem ha00892 : a00892.IsHomogeneous 36 := by
  unfold a00892
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00888.pow 1)))

@[irreducible]
def a00893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00892 ^ 1)
theorem ha00893 : a00893.IsHomogeneous 36 := by
  unfold a00893
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00892.pow 1)))

@[irreducible]
def a00894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00889 ^ 1)
theorem ha00894 : a00894.IsHomogeneous 36 := by
  unfold a00894
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00889.pow 1)))

@[irreducible]
def a00895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00890 ^ 1) + (C ((10 : ℂ) / (27 : ℂ)) * a00894 ^ 1)
theorem ha00895 : a00895.IsHomogeneous 36 := by
  unfold a00895
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (27 : ℂ))).mul (ha00894.pow 1)))

@[irreducible]
def a00896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00895 ^ 1)
theorem ha00896 : a00896.IsHomogeneous 36 := by
  unfold a00896
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00895.pow 1)))

@[irreducible]
def a00897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00893 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00896 ^ 1)
theorem ha00897 : a00897.IsHomogeneous 36 := by
  unfold a00897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00896.pow 1)))

@[irreducible]
def a00898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00600 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00692 ^ 1)
theorem ha00898 : a00898.IsHomogeneous 45 := by
  unfold a00898
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00600.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00692.pow 1)))

@[irreducible]
def a00899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00898 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00692 ^ 1)
theorem ha00899 : a00899.IsHomogeneous 45 := by
  unfold a00899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00898.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00692.pow 1)))

@[irreducible]
def a00900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00898 ^ 1)
theorem ha00900 : a00900.IsHomogeneous 45 := by
  unfold a00900
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00898.pow 1)))

@[irreducible]
def a00901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00899 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00900 ^ 1)
theorem ha00901 : a00901.IsHomogeneous 45 := by
  unfold a00901
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00899.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00900.pow 1)))

@[irreducible]
def a00902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00900 ^ 1)
theorem ha00902 : a00902.IsHomogeneous 45 := by
  unfold a00902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00900.pow 1)))

@[irreducible]
def a00903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00902 ^ 1)
theorem ha00903 : a00903.IsHomogeneous 45 := by
  unfold a00903
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00902.pow 1)))

@[irreducible]
def a00904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00899 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00692 ^ 1)
theorem ha00904 : a00904.IsHomogeneous 45 := by
  unfold a00904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00899.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00692.pow 1)))

@[irreducible]
def a00905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00904 ^ 1)
theorem ha00905 : a00905.IsHomogeneous 45 := by
  unfold a00905
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00904.pow 1)))

@[irreducible]
def a00906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00905 ^ 1)
theorem ha00906 : a00906.IsHomogeneous 45 := by
  unfold a00906
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00905.pow 1)))

@[irreducible]
def a00907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00902 ^ 1)
theorem ha00907 : a00907.IsHomogeneous 45 := by
  unfold a00907
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00902.pow 1)))

@[irreducible]
def a00908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00907 ^ 1)
theorem ha00908 : a00908.IsHomogeneous 45 := by
  unfold a00908
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00907.pow 1)))

@[irreducible]
def a00909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00906 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00908 ^ 1)
theorem ha00909 : a00909.IsHomogeneous 45 := by
  unfold a00909
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00908.pow 1)))

@[irreducible]
def a00910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1)
theorem ha00910 : a00910.IsHomogeneous 39 := by
  unfold a00910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1)))

@[irreducible]
def a00911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00910 ^ 1)
theorem ha00911 : a00911.IsHomogeneous 39 := by
  unfold a00911
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00910.pow 1)))

@[irreducible]
def a00912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00910 ^ 1)
theorem ha00912 : a00912.IsHomogeneous 39 := by
  unfold a00912
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00910.pow 1)))

@[irreducible]
def a00913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00911 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00912 ^ 1)
theorem ha00913 : a00913.IsHomogeneous 39 := by
  unfold a00913
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00911.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00912.pow 1)))

@[irreducible]
def a00914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00911 ^ 1)
theorem ha00914 : a00914.IsHomogeneous 39 := by
  unfold a00914
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00911.pow 1)))

@[irreducible]
def a00915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00607 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00914 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00913 ^ 1)
theorem ha00915 : a00915.IsHomogeneous 39 := by
  unfold a00915
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00914.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00913.pow 1)))

@[irreducible]
def a00916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00910 ^ 1)
theorem ha00916 : a00916.IsHomogeneous 39 := by
  unfold a00916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00910.pow 1)))

@[irreducible]
def a00917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00916 ^ 1)
theorem ha00917 : a00917.IsHomogeneous 39 := by
  unfold a00917
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00916.pow 1)))

@[irreducible]
def a00918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00912 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00916 ^ 1)
theorem ha00918 : a00918.IsHomogeneous 39 := by
  unfold a00918
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00912.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00916.pow 1)))

@[irreducible]
def a00919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00918 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00917 ^ 1)
theorem ha00919 : a00919.IsHomogeneous 39 := by
  unfold a00919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00918.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00917.pow 1)))

@[irreducible]
def a00920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00917 ^ 1)
theorem ha00920 : a00920.IsHomogeneous 39 := by
  unfold a00920
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00917.pow 1)))

@[irreducible]
def a00921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00915 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00920 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00919 ^ 1)
theorem ha00921 : a00921.IsHomogeneous 39 := by
  unfold a00921
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00915.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00920.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00919.pow 1)))

@[irreducible]
def a00922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00916 ^ 1)
theorem ha00922 : a00922.IsHomogeneous 39 := by
  unfold a00922
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00916.pow 1)))

@[irreducible]
def a00923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00917 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00922 ^ 1)
theorem ha00923 : a00923.IsHomogeneous 39 := by
  unfold a00923
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00917.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00922.pow 1)))

@[irreducible]
def a00924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00613 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00922 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00918 ^ 1)
theorem ha00924 : a00924.IsHomogeneous 39 := by
  unfold a00924
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00922.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00918.pow 1)))

@[irreducible]
def a00925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00919 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00923 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00924 ^ 1)
theorem ha00925 : a00925.IsHomogeneous 39 := by
  unfold a00925
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00919.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00923.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00924.pow 1)))

@[irreducible]
def a00926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00923 ^ 1)
theorem ha00926 : a00926.IsHomogeneous 39 := by
  unfold a00926
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00923.pow 1)))

@[irreducible]
def a00927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00921 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00926 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00925 ^ 1)
theorem ha00927 : a00927.IsHomogeneous 39 := by
  unfold a00927
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00921.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00926.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00925.pow 1)))

@[irreducible]
def a00928 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00909 ^ 1) + (C ((7 : ℂ) / (27 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00627 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00897 ^ 1)
theorem ha00928 : a00928.IsHomogeneous 45 := by
  unfold a00928
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00909.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (27 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00627.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00897.pow 1)))

@[irreducible]
def a00929 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00327 ^ 1)
theorem ha00929 : a00929.IsHomogeneous 145 := by
  unfold a00929
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a00930 : Poly := (C ((-1 : ℂ) / (120 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 2 * a00928 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00929 ^ 1)
theorem ha00930 : a00930.IsHomogeneous 145 := by
  unfold a00930
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (120 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 2)).mul (ha00928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00929.pow 1)))

@[irreducible]
def a00931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00930 ^ 1)
theorem ha00931 : a00931.IsHomogeneous 145 := by
  unfold a00931
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00362.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00930.pow 1)))

@[irreducible]
def a00932 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a00362 ^ 1)
theorem ha00932 : a00932.IsHomogeneous 703 := by
  unfold a00932
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha00362.pow 1)))

@[irreducible]
def a00933 : Poly := (C ((-9 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a00883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00932 ^ 1)
theorem ha00933 : a00933.IsHomogeneous 1150 := by
  unfold a00933
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha00883.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00932.pow 1)))

@[irreducible]
def a00934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 3 * a00503 ^ 1)
theorem ha00934 : a00934.IsHomogeneous 1178 := by
  unfold a00934
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00933.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 3)).mul (ha00503.pow 1)))

@[irreducible]
def a00935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00934 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00327 ^ 1 * a00364 ^ 1)
theorem ha00935 : a00935.IsHomogeneous 1178 := by
  unfold a00935
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00934.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00327.pow 1)).mul (ha00364.pow 1)))

@[irreducible]
def a00936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00362 ^ 1 * a00364 ^ 1) + (C ((9 : ℂ) / (625 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a00935 ^ 1)
theorem ha00936 : a00936.IsHomogeneous 1239 := by
  unfold a00936
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00362.pow 1)).mul (ha00364.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (625 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha00935.pow 1)))

@[irreducible]
def a00937 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00117 ^ 1 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a00446 ^ 1)
theorem ha00937 : a00937.IsHomogeneous 1246 := by
  unfold a00937
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00936.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00117.pow 1)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha00446.pow 1)))

@[irreducible]
def a00938 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((-1 : ℂ) / (2880 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00046 ^ 1) + (C ((1 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00082 ^ 1)
theorem ha00938 : a00938.IsHomogeneous 67 := by
  unfold a00938
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2880 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00046.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00939 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00100 ^ 1)
theorem ha00939 : a00939.IsHomogeneous 60 := by
  unfold a00939
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00082.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00125 ^ 1 * a00938 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00101 ^ 1 * a00939 ^ 1)
theorem ha00940 : a00940.IsHomogeneous 141 := by
  unfold a00940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00125.pow 1)).mul (ha00938.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00101.pow 1)).mul (ha00939.pow 1)))

@[irreducible]
def a00941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00007 ^ 1 * a00014 ^ 4 * a00025 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1) + (C ((25 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00148 ^ 1 * a00368 ^ 1)
theorem ha00941 : a00941.IsHomogeneous 151 := by
  unfold a00941
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00148.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00941 ^ 1) + (C ((50 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00025 ^ 1 * a00389 ^ 1)
theorem ha00942 : a00942.IsHomogeneous 151 := by
  unfold a00942
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00941.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00025.pow 1)).mul (ha00389.pow 1)))

@[irreducible]
def a00943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1)
theorem ha00943 : a00943.IsHomogeneous 31 := by
  unfold a00943
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)))

@[irreducible]
def a00944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00943 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1)
theorem ha00944 : a00944.IsHomogeneous 31 := by
  unfold a00944
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00943.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)))

@[irreducible]
def a00945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00943 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00944 ^ 1)
theorem ha00945 : a00945.IsHomogeneous 31 := by
  unfold a00945
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00944.pow 1)))

@[irreducible]
def a00946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1)
theorem ha00946 : a00946.IsHomogeneous 24 := by
  unfold a00946
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)))

@[irreducible]
def a00947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00946 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1)
theorem ha00947 : a00947.IsHomogeneous 24 := by
  unfold a00947
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00946.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)))

@[irreducible]
def a00948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00946 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1)
theorem ha00948 : a00948.IsHomogeneous 24 := by
  unfold a00948
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00946.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)))

@[irreducible]
def a00949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00947 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00948 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1)
theorem ha00949 : a00949.IsHomogeneous 24 := by
  unfold a00949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00948.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)))

@[irreducible]
def a00950 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00025 ^ 1 * a00949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00945 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 13 * a00001 ^ 3 * a00002 ^ 1 * a00003 ^ 5 * a00004 ^ 3 * a00032 ^ 2)
theorem ha00950 : a00950.IsHomogeneous 37 := by
  unfold a00950
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00945.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 13)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00003.pow 5)).mul (ha00004.pow 3)).mul (ha00032.pow 2)))

@[irreducible]
def a00951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00370 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00100 ^ 1 * a00950 ^ 1)
theorem ha00951 : a00951.IsHomogeneous 73 := by
  unfold a00951
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00370.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00100.pow 1)).mul (ha00950.pow 1)))

@[irreducible]
def a00952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a00393 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 1 * a00951 ^ 1)
theorem ha00952 : a00952.IsHomogeneous 145 := by
  unfold a00952
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha00393.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00951.pow 1)))

@[irreducible]
def a00953 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00007 ^ 1 * a00009 ^ 2) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00007 ^ 1)
theorem ha00953 : a00953.IsHomogeneous 24 := by
  unfold a00953
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00007.pow 1)))

@[irreducible]
def a00954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00146 ^ 1 * a00372 ^ 1) + (C ((48 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00953 ^ 1)
theorem ha00954 : a00954.IsHomogeneous 121 := by
  unfold a00954
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00146.pow 1)).mul (ha00372.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00953.pow 1)))

@[irreducible]
def a00955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00954 ^ 1) + (C ((96 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a00138 ^ 1 * a00387 ^ 1)
theorem ha00955 : a00955.IsHomogeneous 121 := by
  unfold a00955
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00954.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((96 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha00138.pow 1)).mul (ha00387.pow 1)))

@[irreducible]
def a00956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00368 ^ 1)
theorem ha00956 : a00956.IsHomogeneous 36 := by
  unfold a00956
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00368.pow 1)))

@[irreducible]
def a00957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00956 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00025 ^ 1)
theorem ha00957 : a00957.IsHomogeneous 36 := by
  unfold a00957
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00956.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00025.pow 1)))

@[irreducible]
def a00958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00957 ^ 1)
theorem ha00958 : a00958.IsHomogeneous 36 := by
  unfold a00958
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00957.pow 1)))

@[irreducible]
def a00959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00375 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00958 ^ 1)
theorem ha00959 : a00959.IsHomogeneous 85 := by
  unfold a00959
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00375.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00958.pow 1)))

@[irreducible]
def a00960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00959 ^ 1) + (C ((48 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00139 ^ 1)
theorem ha00960 : a00960.IsHomogeneous 85 := by
  unfold a00960
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00959.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00139.pow 1)))

@[irreducible]
def a00961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00046 ^ 1 * a00126 ^ 1) + (C ((3 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00960 ^ 1)
theorem ha00961 : a00961.IsHomogeneous 91 := by
  unfold a00961
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00046.pow 1)).mul (ha00126.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00960.pow 1)))

@[irreducible]
def a00962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00368 ^ 1)
theorem ha00962 : a00962.IsHomogeneous 36 := by
  unfold a00962
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00368.pow 1)))

@[irreducible]
def a00963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00962 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00025 ^ 1)
theorem ha00963 : a00963.IsHomogeneous 36 := by
  unfold a00963
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00962.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00025.pow 1)))

@[irreducible]
def a00964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00379 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00963 ^ 1)
theorem ha00964 : a00964.IsHomogeneous 85 := by
  unfold a00964
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00379.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00963.pow 1)))

@[irreducible]
def a00965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00964 ^ 1) + (C ((72 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00141 ^ 1)
theorem ha00965 : a00965.IsHomogeneous 85 := by
  unfold a00965
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00964.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00141.pow 1)))

@[irreducible]
def a00966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00046 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (96 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00965 ^ 1)
theorem ha00966 : a00966.IsHomogeneous 91 := by
  unfold a00966
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00046.pow 1)).mul (ha00126.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00965.pow 1)))

@[irreducible]
def a00967 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00966 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00961 ^ 1)
theorem ha00967 : a00967.IsHomogeneous 91 := by
  unfold a00967
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00966.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00961.pow 1)))

@[irreducible]
def a00968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00368 ^ 1)
theorem ha00968 : a00968.IsHomogeneous 36 := by
  unfold a00968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00368.pow 1)))

@[irreducible]
def a00969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00968 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00025 ^ 1)
theorem ha00969 : a00969.IsHomogeneous 36 := by
  unfold a00969
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00968.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00025.pow 1)))

@[irreducible]
def a00970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00969 ^ 1)
theorem ha00970 : a00970.IsHomogeneous 36 := by
  unfold a00970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00969.pow 1)))

@[irreducible]
def a00971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00384 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00970 ^ 1)
theorem ha00971 : a00971.IsHomogeneous 85 := by
  unfold a00971
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00384.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00970.pow 1)))

@[irreducible]
def a00972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00971 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00144 ^ 1)
theorem ha00972 : a00972.IsHomogeneous 85 := by
  unfold a00972
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00971.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00144.pow 1)))

@[irreducible]
def a00973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00046 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00972 ^ 1)
theorem ha00973 : a00973.IsHomogeneous 91 := by
  unfold a00973
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00046.pow 1)).mul (ha00126.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00972.pow 1)))

@[irreducible]
def a00974 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00973 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00967 ^ 1)
theorem ha00974 : a00974.IsHomogeneous 91 := by
  unfold a00974
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00973.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00967.pow 1)))

@[irreducible]
def a00975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00127 ^ 1 * a00974 ^ 1) + (C ((1 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00955 ^ 1)
theorem ha00975 : a00975.IsHomogeneous 127 := by
  unfold a00975
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00127.pow 1)).mul (ha00974.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00955.pow 1)))

@[irreducible]
def a00976 : Poly := (C ((-3 : ℂ) / (2560 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00952 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 4 * a00975 ^ 1)
theorem ha00976 : a00976.IsHomogeneous 151 := by
  unfold a00976
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2560 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00952.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 4)).mul (ha00975.pow 1)))

@[irreducible]
def a00977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00976 ^ 1) + (C ((3 : ℂ) / (200 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 4 * a00942 ^ 1)
theorem ha00977 : a00977.IsHomogeneous 181 := by
  unfold a00977
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00976.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (200 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 4)).mul (ha00942.pow 1)))

@[irreducible]
def a00978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1)
theorem ha00978 : a00978.IsHomogeneous 55 := by
  unfold a00978
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00395 ^ 1) + (C ((72 : ℂ) / (25 : ℂ)) * a00100 ^ 1 * a00978 ^ 1)
theorem ha00979 : a00979.IsHomogeneous 91 := by
  unfold a00979
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00395.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (25 : ℂ))).mul (ha00100.pow 1)).mul (ha00978.pow 1)))

@[irreducible]
def a00980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00046 ^ 1 * a00100 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00061 ^ 1 * a00082 ^ 1)
theorem ha00980 : a00980.IsHomogeneous 87 := by
  unfold a00980
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00100.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00061.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00980 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00061 ^ 1 * a00082 ^ 1)
theorem ha00981 : a00981.IsHomogeneous 87 := by
  unfold a00981
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00980.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00061.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00046 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00981 ^ 1)
theorem ha00982 : a00982.IsHomogeneous 87 := by
  unfold a00982
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00981.pow 1)))

@[irreducible]
def a00983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00982 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00082 ^ 1 * a00393 ^ 1)
theorem ha00983 : a00983.IsHomogeneous 136 := by
  unfold a00983
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00982.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a00984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00983 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00082 ^ 1 * a00100 ^ 1)
theorem ha00984 : a00984.IsHomogeneous 136 := by
  unfold a00984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00983.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00046 ^ 1 * a00100 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00984 ^ 1)
theorem ha00985 : a00985.IsHomogeneous 136 := by
  unfold a00985
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00046.pow 1)).mul (ha00100.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00984.pow 1)))

@[irreducible]
def a00986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00985 ^ 1) + (C ((5 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00979 ^ 1)
theorem ha00986 : a00986.IsHomogeneous 160 := by
  unfold a00986
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00985.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00979.pow 1)))

@[irreducible]
def a00987 : Poly := (C ((-25 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00042 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00396 ^ 1) + (C ((-25 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00150 ^ 1 * a00398 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00126 ^ 2 * a00127 ^ 1 * a00986 ^ 1)
theorem ha00987 : a00987.IsHomogeneous 304 := by
  unfold a00987
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00396.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00150.pow 1)).mul (ha00398.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00986.pow 1)))

@[irreducible]
def a00988 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00042 ^ 2 * a00100 ^ 2 * a00977 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00987 ^ 1)
theorem ha00988 : a00988.IsHomogeneous 304 := by
  unfold a00988
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha00977.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00987.pow 1)))

@[irreducible]
def a00989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00368 ^ 1)
theorem ha00989 : a00989.IsHomogeneous 36 := by
  unfold a00989
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00126.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00368.pow 1)))

@[irreducible]
def a00990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00989 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00368 ^ 1)
theorem ha00990 : a00990.IsHomogeneous 36 := by
  unfold a00990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00989.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00368.pow 1)))

@[irreducible]
def a00991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00990 ^ 1)
theorem ha00991 : a00991.IsHomogeneous 36 := by
  unfold a00991
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00990.pow 1)))

@[irreducible]
def a00992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00127 ^ 1 * a00991 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00138 ^ 1 * a00400 ^ 1)
theorem ha00992 : a00992.IsHomogeneous 72 := by
  unfold a00992
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00127.pow 1)).mul (ha00991.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00138.pow 1)).mul (ha00400.pow 1)))

@[irreducible]
def a00993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00992 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00372 ^ 1)
theorem ha00993 : a00993.IsHomogeneous 72 := by
  unfold a00993
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00992.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00372.pow 1)))

@[irreducible]
def a00994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a00993 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00126 ^ 2 * a00953 ^ 1)
theorem ha00994 : a00994.IsHomogeneous 84 := by
  unfold a00994
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha00993.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00126.pow 2)).mul (ha00953.pow 1)))

@[irreducible]
def a00995 : Poly := (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00082 ^ 1 * a00404 ^ 1) + (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a00393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a00982 ^ 1)
theorem ha00995 : a00995.IsHomogeneous 220 := by
  unfold a00995
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha00404.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00393.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a00996 : Poly := (C ((-3 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 3 * a00994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00995 ^ 1)
theorem ha00996 : a00996.IsHomogeneous 220 := by
  unfold a00996
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 3)).mul (ha00994.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00995.pow 1)))

@[irreducible]
def a00997 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 2 * a00126 ^ 2 * a00127 ^ 1 * a00940 ^ 1) + (C ((-1 : ℂ) / (25600 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 4 * a00136 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a00125 ^ 1 * a00988 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 3 * a00125 ^ 1 * a00996 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 3 * a00042 ^ 3 * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a00367 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00367 ^ 1) + (C ((25 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 3 * a00136 ^ 1 * a00404 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 1 * a00136 ^ 1 * a00398 ^ 1)
theorem ha00997 : a00997.IsHomogeneous 395 := by
  unfold a00997
  exact ((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00940.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (25600 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 4)).mul (ha00136.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00125.pow 1)).mul (ha00988.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00125.pow 1)).mul (ha00996.pow 1))).add (((((((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00367.pow 1))).add (((((((((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00367.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00136.pow 1)).mul (ha00404.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 1)).mul (ha00136.pow 1)).mul (ha00398.pow 1)))

@[irreducible]
def a00998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00368 ^ 1)
theorem ha00998 : a00998.IsHomogeneous 6 := by
  unfold a00998
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00368.pow 1)))

@[irreducible]
def a00999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00962 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00998 ^ 1)
theorem ha00999 : a00999.IsHomogeneous 36 := by
  unfold a00999
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00962.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00998.pow 1)))

@[irreducible]
def a01000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00962 ^ 1)
theorem ha01000 : a01000.IsHomogeneous 36 := by
  unfold a01000
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00962.pow 1)))

@[irreducible]
def a01001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00999 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01000 ^ 1)
theorem ha01001 : a01001.IsHomogeneous 36 := by
  unfold a01001
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01000.pow 1)))

@[irreducible]
def a01002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (96 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00025 ^ 1)
theorem ha01002 : a01002.IsHomogeneous 36 := by
  unfold a01002
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00126.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00025.pow 1)))

@[irreducible]
def a01003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01002 ^ 1) + (C ((1 : ℂ) / (96 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00998 ^ 1)
theorem ha01003 : a01003.IsHomogeneous 36 := by
  unfold a01003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01002.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00998.pow 1)))

@[irreducible]
def a01004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00999 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01003 ^ 1)
theorem ha01004 : a01004.IsHomogeneous 36 := by
  unfold a01004
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01003.pow 1)))

@[irreducible]
def a01005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01001 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01004 ^ 1)
theorem ha01005 : a01005.IsHomogeneous 36 := by
  unfold a01005
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01004.pow 1)))

@[irreducible]
def a01006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00040 ^ 1)
theorem ha01006 : a01006.IsHomogeneous 18 := by
  unfold a01006
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00040.pow 1)))

@[irreducible]
def a01007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a00040 ^ 1)
theorem ha01007 : a01007.IsHomogeneous 39 := by
  unfold a01007
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha00040.pow 1)))

@[irreducible]
def a01008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01007 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a01006 ^ 1)
theorem ha01008 : a01008.IsHomogeneous 40 := by
  unfold a01008
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01007.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha01006.pow 1)))

@[irreducible]
def a01009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00007 ^ 1 * a00064 ^ 1) + (C ((1 : ℂ) / (864 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1 * a00155 ^ 1)
theorem ha01009 : a01009.IsHomogeneous 46 := by
  unfold a01009
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00007.pow 1)).mul (ha00064.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a01010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01009 ^ 1) + (C ((1 : ℂ) / (864 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01006 ^ 1)
theorem ha01010 : a01010.IsHomogeneous 46 := by
  unfold a01010
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01009.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01006.pow 1)))

@[irreducible]
def a01011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01010 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01008 ^ 1)
theorem ha01011 : a01011.IsHomogeneous 46 := by
  unfold a01011
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01010.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01008.pow 1)))

@[irreducible]
def a01012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01007 ^ 1)
theorem ha01012 : a01012.IsHomogeneous 39 := by
  unfold a01012
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01007.pow 1)))

@[irreducible]
def a01013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01008 ^ 1)
theorem ha01013 : a01013.IsHomogeneous 40 := by
  unfold a01013
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01008.pow 1)))

@[irreducible]
def a01014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01011 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01013 ^ 1)
theorem ha01014 : a01014.IsHomogeneous 46 := by
  unfold a01014
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01013.pow 1)))

@[irreducible]
def a01015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00052 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00037 ^ 1)
theorem ha01015 : a01015.IsHomogeneous 36 := by
  unfold a01015
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00052.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00037.pow 1)))

@[irreducible]
def a01016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00038 ^ 1)
theorem ha01016 : a01016.IsHomogeneous 6 := by
  unfold a01016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00038.pow 1)))

@[irreducible]
def a01017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01015 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01016 ^ 1)
theorem ha01017 : a01017.IsHomogeneous 36 := by
  unfold a01017
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01015.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01016.pow 1)))

@[irreducible]
def a01018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00055 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2)
theorem ha01018 : a01018.IsHomogeneous 36 := by
  unfold a01018
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00055.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)))

@[irreducible]
def a01019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01018 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01016 ^ 1)
theorem ha01019 : a01019.IsHomogeneous 36 := by
  unfold a01019
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01018.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01016.pow 1)))

@[irreducible]
def a01020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01019 ^ 1)
theorem ha01020 : a01020.IsHomogeneous 36 := by
  unfold a01020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01017.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01019.pow 1)))

@[irreducible]
def a01021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00133 ^ 1)
theorem ha01021 : a01021.IsHomogeneous 19 := by
  unfold a01021
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a01022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01021 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00133 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a00156 ^ 1)
theorem ha01022 : a01022.IsHomogeneous 19 := by
  unfold a01022
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01021.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00133.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a01023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a01022 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a00436 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00060 ^ 1 * a00133 ^ 1)
theorem ha01023 : a01023.IsHomogeneous 31 := by
  unfold a01023
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha01022.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha00436.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00060.pow 1)).mul (ha00133.pow 1)))

end CycleQ2Concrete
