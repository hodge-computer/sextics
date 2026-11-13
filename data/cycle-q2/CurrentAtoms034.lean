import Proposal.CurrentAtoms033

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a10496 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1 * a00864 ^ 1)
theorem ha10496 : a10496.IsHomogeneous 96 := by
  unfold a10496
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a10496 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10493 ^ 1)
theorem ha10497 : a10497.IsHomogeneous 132 := by
  unfold a10497
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha10496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10493.pow 1)))

@[irreducible]
def a10498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10495 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10497 ^ 1)
theorem ha10498 : a10498.IsHomogeneous 132 := by
  unfold a10498
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10495.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10497.pow 1)))

@[irreducible]
def a10499 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02007 ^ 1)
theorem ha10499 : a10499.IsHomogeneous 54 := by
  unfold a10499
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10500 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a10499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10496 ^ 1)
theorem ha10500 : a10500.IsHomogeneous 96 := by
  unfold a10500
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10496.pow 1)))

@[irreducible]
def a10501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a10500 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10497 ^ 1)
theorem ha10501 : a10501.IsHomogeneous 132 := by
  unfold a10501
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha10500.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10497.pow 1)))

@[irreducible]
def a10502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10501 ^ 1)
theorem ha10502 : a10502.IsHomogeneous 132 := by
  unfold a10502
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10501.pow 1)))

@[irreducible]
def a10503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07368 ^ 1)
theorem ha10503 : a10503.IsHomogeneous 135 := by
  unfold a10503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07368.pow 1)))

@[irreducible]
def a10504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10494 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10503 ^ 1)
theorem ha10504 : a10504.IsHomogeneous 135 := by
  unfold a10504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10494.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10503.pow 1)))

@[irreducible]
def a10505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10504 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10495 ^ 1)
theorem ha10505 : a10505.IsHomogeneous 135 := by
  unfold a10505
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10504.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10495.pow 1)))

@[irreducible]
def a10506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10505 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10498 ^ 1)
theorem ha10506 : a10506.IsHomogeneous 135 := by
  unfold a10506
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10505.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10498.pow 1)))

@[irreducible]
def a10507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10506 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10502 ^ 1)
theorem ha10507 : a10507.IsHomogeneous 135 := by
  unfold a10507
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10502.pow 1)))

@[irreducible]
def a10508 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02847 ^ 1)
theorem ha10508 : a10508.IsHomogeneous 154 := by
  unfold a10508
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01281.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02847.pow 1)))

@[irreducible]
def a10509 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00487 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01281 ^ 1)
theorem ha10509 : a10509.IsHomogeneous 148 := by
  unfold a10509
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00487.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a10510 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a10509 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10508 ^ 1)
theorem ha10510 : a10510.IsHomogeneous 154 := by
  unfold a10510
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha10509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10508.pow 1)))

@[irreducible]
def a10511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a02847 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00129 ^ 1 * a05610 ^ 1)
theorem ha10511 : a10511.IsHomogeneous 160 := by
  unfold a10511
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha02847.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00129.pow 1)).mul (ha05610.pow 1)))

@[irreducible]
def a10512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10511 ^ 1)
theorem ha10512 : a10512.IsHomogeneous 160 := by
  unfold a10512
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10511.pow 1)))

@[irreducible]
def a10513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10512 ^ 1)
theorem ha10513 : a10513.IsHomogeneous 160 := by
  unfold a10513
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10512.pow 1)))

@[irreducible]
def a10514 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00487 ^ 1 * a02008 ^ 1)
theorem ha10514 : a10514.IsHomogeneous 103 := by
  unfold a10514
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a10515 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10514 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10509 ^ 1)
theorem ha10515 : a10515.IsHomogeneous 148 := by
  unfold a10515
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10509.pow 1)))

@[irreducible]
def a10516 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a10515 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10510 ^ 1)
theorem ha10516 : a10516.IsHomogeneous 154 := by
  unfold a10516
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha10515.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10510.pow 1)))

@[irreducible]
def a10517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10513 ^ 1)
theorem ha10517 : a10517.IsHomogeneous 160 := by
  unfold a10517
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10513.pow 1)))

@[irreducible]
def a10518 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01275 ^ 1 * a01702 ^ 1)
theorem ha10518 : a10518.IsHomogeneous 142 := by
  unfold a10518
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01275.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a10519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01275 ^ 1 * a01702 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00484 ^ 1 * a03562 ^ 1)
theorem ha10519 : a10519.IsHomogeneous 142 := by
  unfold a10519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01275.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00484.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10519 ^ 1)
theorem ha10520 : a10520.IsHomogeneous 142 := by
  unfold a10520
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10519.pow 1)))

@[irreducible]
def a10521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05595 ^ 1)
theorem ha10521 : a10521.IsHomogeneous 143 := by
  unfold a10521
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a10522 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a10521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10518 ^ 1)
theorem ha10522 : a10522.IsHomogeneous 143 := by
  unfold a10522
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha10521.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10518.pow 1)))

@[irreducible]
def a10523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10522 ^ 1)
theorem ha10523 : a10523.IsHomogeneous 143 := by
  unfold a10523
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10522.pow 1)))

@[irreducible]
def a10524 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a06725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a03562 ^ 1)
theorem ha10524 : a10524.IsHomogeneous 136 := by
  unfold a10524
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10519 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a10524 ^ 1)
theorem ha10525 : a10525.IsHomogeneous 142 := by
  unfold a10525
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10519.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha10524.pow 1)))

@[irreducible]
def a10526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10525 ^ 1)
theorem ha10526 : a10526.IsHomogeneous 142 := by
  unfold a10526
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10525.pow 1)))

@[irreducible]
def a10527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10523 ^ 1)
theorem ha10527 : a10527.IsHomogeneous 143 := by
  unfold a10527
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10526.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10523.pow 1)))

@[irreducible]
def a10528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00712 ^ 1 * a01678 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00691 ^ 1 * a01702 ^ 1)
theorem ha10528 : a10528.IsHomogeneous 104 := by
  unfold a10528
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00691.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a10529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a01678 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a03534 ^ 1)
theorem ha10529 : a10529.IsHomogeneous 98 := by
  unfold a10529
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha01678.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a10530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10528 ^ 1)
theorem ha10530 : a10530.IsHomogeneous 104 := by
  unfold a10530
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10528.pow 1)))

@[irreducible]
def a10531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01702 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00241 ^ 1 * a03562 ^ 1)
theorem ha10531 : a10531.IsHomogeneous 106 := by
  unfold a10531
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10528 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a10531 ^ 1)
theorem ha10532 : a10532.IsHomogeneous 106 := by
  unfold a10532
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha10531.pow 1)))

@[irreducible]
def a10533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10532 ^ 1)
theorem ha10533 : a10533.IsHomogeneous 106 := by
  unfold a10533
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10532.pow 1)))

@[irreducible]
def a10534 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a06692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03534 ^ 1)
theorem ha10534 : a10534.IsHomogeneous 92 := by
  unfold a10534
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06692.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a10535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10529 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a10534 ^ 1)
theorem ha10535 : a10535.IsHomogeneous 98 := by
  unfold a10535
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10529.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha10534.pow 1)))

@[irreducible]
def a10536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10530 ^ 1)
theorem ha10536 : a10536.IsHomogeneous 104 := by
  unfold a10536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10530.pow 1)))

@[irreducible]
def a10537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10533 ^ 1)
theorem ha10537 : a10537.IsHomogeneous 106 := by
  unfold a10537
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10536.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10533.pow 1)))

@[irreducible]
def a10538 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00241 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a06725 ^ 1)
theorem ha10538 : a10538.IsHomogeneous 100 := by
  unfold a10538
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00241.pow 1)).mul (ha03562.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a10539 : Poly := (C ((-15 : ℂ) / (2 : ℂ)) * a10531 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10538 ^ 1)
theorem ha10539 : a10539.IsHomogeneous 106 := by
  unfold a10539
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (2 : ℂ))).mul (ha10531.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10538.pow 1)))

@[irreducible]
def a10540 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a10539 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10532 ^ 1)
theorem ha10540 : a10540.IsHomogeneous 106 := by
  unfold a10540
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha10539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10532.pow 1)))

@[irreducible]
def a10541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10540 ^ 1)
theorem ha10541 : a10541.IsHomogeneous 106 := by
  unfold a10541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10533.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10540.pow 1)))

@[irreducible]
def a10542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10541 ^ 1)
theorem ha10542 : a10542.IsHomogeneous 106 := by
  unfold a10542
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10541.pow 1)))

@[irreducible]
def a10543 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a10542 ^ 1)
theorem ha10543 : a10543.IsHomogeneous 143 := by
  unfold a10543
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05595.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha10542.pow 1)))

@[irreducible]
def a10544 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a10543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10521 ^ 1)
theorem ha10544 : a10544.IsHomogeneous 143 := by
  unfold a10544
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha10543.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10521.pow 1)))

@[irreducible]
def a10545 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a10544 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10522 ^ 1)
theorem ha10545 : a10545.IsHomogeneous 143 := by
  unfold a10545
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha10544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10522.pow 1)))

@[irreducible]
def a10546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10545 ^ 1)
theorem ha10546 : a10546.IsHomogeneous 143 := by
  unfold a10546
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10523.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10545.pow 1)))

@[irreducible]
def a10547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10527 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10546 ^ 1)
theorem ha10547 : a10547.IsHomogeneous 143 := by
  unfold a10547
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10527.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10546.pow 1)))

@[irreducible]
def a10548 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00829 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a01938 ^ 1)
theorem ha10548 : a10548.IsHomogeneous 143 := by
  unfold a10548
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00829.pow 1)).mul (ha01678.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a10549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a03534 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00829 ^ 1 * a01678 ^ 1)
theorem ha10549 : a10549.IsHomogeneous 137 := by
  unfold a10549
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00829.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a10550 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a10549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10548 ^ 1)
theorem ha10550 : a10550.IsHomogeneous 143 := by
  unfold a10550
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha10549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10548.pow 1)))

@[irreducible]
def a10551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a03963 ^ 1)
theorem ha10551 : a10551.IsHomogeneous 142 := by
  unfold a10551
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a10552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10548 ^ 1)
theorem ha10552 : a10552.IsHomogeneous 143 := by
  unfold a10552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10548.pow 1)))

@[irreducible]
def a10553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10552 ^ 1)
theorem ha10553 : a10553.IsHomogeneous 143 := by
  unfold a10553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10552.pow 1)))

@[irreducible]
def a10554 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a06692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03534 ^ 1)
theorem ha10554 : a10554.IsHomogeneous 92 := by
  unfold a10554
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06692.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a10555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10554 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10549 ^ 1)
theorem ha10555 : a10555.IsHomogeneous 137 := by
  unfold a10555
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10549.pow 1)))

@[irreducible]
def a10556 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a10555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10550 ^ 1)
theorem ha10556 : a10556.IsHomogeneous 143 := by
  unfold a10556
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha10555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10550.pow 1)))

@[irreducible]
def a10557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10556 ^ 1)
theorem ha10557 : a10557.IsHomogeneous 143 := by
  unfold a10557
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10556.pow 1)))

@[irreducible]
def a10558 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00241 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a07363 ^ 1)
theorem ha10558 : a10558.IsHomogeneous 142 := by
  unfold a10558
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00241.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a10559 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a10558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10551 ^ 1)
theorem ha10559 : a10559.IsHomogeneous 142 := by
  unfold a10559
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha10558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10551.pow 1)))

@[irreducible]
def a10560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10552 ^ 1)
theorem ha10560 : a10560.IsHomogeneous 143 := by
  unfold a10560
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10552.pow 1)))

@[irreducible]
def a10561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10560 ^ 1)
theorem ha10561 : a10561.IsHomogeneous 143 := by
  unfold a10561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10560.pow 1)))

@[irreducible]
def a10562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10557 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10561 ^ 1)
theorem ha10562 : a10562.IsHomogeneous 143 := by
  unfold a10562
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10561.pow 1)))

@[irreducible]
def a10563 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a10562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10547 ^ 1)
theorem ha10563 : a10563.IsHomogeneous 143 := by
  unfold a10563
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha10562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10547.pow 1)))

@[irreducible]
def a10564 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a10563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a05610 ^ 1)
theorem ha10564 : a10564.IsHomogeneous 167 := by
  unfold a10564
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha10563.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha05610.pow 1)))

@[irreducible]
def a10565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10511 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a10564 ^ 1)
theorem ha10565 : a10565.IsHomogeneous 167 := by
  unfold a10565
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10511.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha10564.pow 1)))

@[irreducible]
def a10566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10512 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10565 ^ 1)
theorem ha10566 : a10566.IsHomogeneous 167 := by
  unfold a10566
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10512.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10565.pow 1)))

@[irreducible]
def a10567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10513 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10566 ^ 1)
theorem ha10567 : a10567.IsHomogeneous 167 := by
  unfold a10567
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10566.pow 1)))

@[irreducible]
def a10568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10517 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10567 ^ 1)
theorem ha10568 : a10568.IsHomogeneous 167 := by
  unfold a10568
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10517.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10567.pow 1)))

@[irreducible]
def a10569 : Poly := (C ((-54 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a10507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10568 ^ 1)
theorem ha10569 : a10569.IsHomogeneous 167 := by
  unfold a10569
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-54 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha10507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10568.pow 1)))

@[irreducible]
def a10570 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a10569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a05615 ^ 1)
theorem ha10570 : a10570.IsHomogeneous 275 := by
  unfold a10570
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha10569.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha05615.pow 1)))

@[irreducible]
def a10571 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a10570 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10490 ^ 1)
theorem ha10571 : a10571.IsHomogeneous 367 := by
  unfold a10571
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha10570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10490.pow 1)))

@[irreducible]
def a10572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10491 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10571 ^ 1)
theorem ha10572 : a10572.IsHomogeneous 427 := by
  unfold a10572
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10491.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10571.pow 1)))

@[irreducible]
def a10573 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a10572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10492 ^ 1)
theorem ha10573 : a10573.IsHomogeneous 451 := by
  unfold a10573
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha10572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10492.pow 1)))

@[irreducible]
def a10574 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a03978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a07382 ^ 1)
theorem ha10574 : a10574.IsHomogeneous 475 := by
  unfold a10574
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha03978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha07382.pow 1)))

@[irreducible]
def a10575 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a10488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10574 ^ 1)
theorem ha10575 : a10575.IsHomogeneous 475 := by
  unfold a10575
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha10488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10574.pow 1)))

@[irreducible]
def a10576 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a10489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10575 ^ 1)
theorem ha10576 : a10576.IsHomogeneous 475 := by
  unfold a10576
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha10489.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10575.pow 1)))

@[irreducible]
def a10577 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a10492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10576 ^ 1)
theorem ha10577 : a10577.IsHomogeneous 475 := by
  unfold a10577
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha10492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10576.pow 1)))

@[irreducible]
def a10578 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a10573 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10577 ^ 1)
theorem ha10578 : a10578.IsHomogeneous 475 := by
  unfold a10578
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha10573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10577.pow 1)))

@[irreducible]
def a10579 : Poly := (C ((-25 : ℂ) / (354294 : ℂ)) * a00003 ^ 2 * a00042 ^ 5 * a00100 ^ 5 * a10486 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a10578 ^ 1)
theorem ha10579 : a10579.IsHomogeneous 493 := by
  unfold a10579
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (354294 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha10486.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha10578.pow 1)))

@[irreducible]
def a10580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a05623 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a10579 ^ 1)
theorem ha10580 : a10580.IsHomogeneous 493 := by
  unfold a10580
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha05623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha10579.pow 1)))

@[irreducible]
def a10581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10216 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10580 ^ 1)
theorem ha10581 : a10581.IsHomogeneous 493 := by
  unfold a10581
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10216.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10580.pow 1)))

@[irreducible]
def a10582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10217 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a10581 ^ 1)
theorem ha10582 : a10582.IsHomogeneous 493 := by
  unfold a10582
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10217.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha10581.pow 1)))

@[irreducible]
def a10583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10218 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10582 ^ 1)
theorem ha10583 : a10583.IsHomogeneous 493 := by
  unfold a10583
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10218.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10582.pow 1)))

@[irreducible]
def a10584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10583 ^ 1)
theorem ha10584 : a10584.IsHomogeneous 493 := by
  unfold a10584
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10222.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10583.pow 1)))

@[irreducible]
def a10585 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a05627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a10584 ^ 1)
theorem ha10585 : a10585.IsHomogeneous 919 := by
  unfold a10585
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha05627.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha10584.pow 1)))

@[irreducible]
def a10586 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a10206 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10585 ^ 1)
theorem ha10586 : a10586.IsHomogeneous 1252 := by
  unfold a10586
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha10206.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10585.pow 1)))

@[irreducible]
def a10587 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a10207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10586 ^ 1)
theorem ha10587 : a10587.IsHomogeneous 1585 := by
  unfold a10587
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha10207.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10586.pow 1)))

@[irreducible]
def a10588 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a10208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10587 ^ 1)
theorem ha10588 : a10588.IsHomogeneous 1918 := by
  unfold a10588
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha10208.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10587.pow 1)))

@[irreducible]
def a10589 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a10212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10588 ^ 1)
theorem ha10589 : a10589.IsHomogeneous 2251 := by
  unfold a10589
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha10212.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10588.pow 1)))

@[irreducible]
def a10590 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a01313 ^ 1 * a01886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02904 ^ 1)
theorem ha10590 : a10590.IsHomogeneous 1393 := by
  unfold a10590
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha01313.pow 1)).mul (ha01886.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a10591 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01313 ^ 1 * a01886 ^ 1)
theorem ha10591 : a10591.IsHomogeneous 1690 := by
  unfold a10591
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01313.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a10592 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a10591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10590 ^ 1)
theorem ha10592 : a10592.IsHomogeneous 1726 := by
  unfold a10592
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha10591.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10590.pow 1)))

@[irreducible]
def a10593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a05699 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a02904 ^ 1)
theorem ha10593 : a10593.IsHomogeneous 1096 := by
  unfold a10593
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha05699.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a10594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10593 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10590 ^ 1)
theorem ha10594 : a10594.IsHomogeneous 1429 := by
  unfold a10594
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10593.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10590.pow 1)))

@[irreducible]
def a10595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10594 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10592 ^ 1)
theorem ha10595 : a10595.IsHomogeneous 1762 := by
  unfold a10595
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10594.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10592.pow 1)))

@[irreducible]
def a10596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a03873 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a07222 ^ 1)
theorem ha10596 : a10596.IsHomogeneous 1987 := by
  unfold a10596
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha03873.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a10597 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a10596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10591 ^ 1)
theorem ha10597 : a10597.IsHomogeneous 2023 := by
  unfold a10597
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha10596.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10591.pow 1)))

@[irreducible]
def a10598 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a10597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10592 ^ 1)
theorem ha10598 : a10598.IsHomogeneous 2059 := by
  unfold a10598
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha10597.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10592.pow 1)))

@[irreducible]
def a10599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10595 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10598 ^ 1)
theorem ha10599 : a10599.IsHomogeneous 2095 := by
  unfold a10599
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10598.pow 1)))

@[irreducible]
def a10600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02901 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a01311 ^ 1 * a01976 ^ 1)
theorem ha10600 : a10600.IsHomogeneous 337 := by
  unfold a10600
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02901.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha01311.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a10601 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a01311 ^ 1 * a01976 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00500 ^ 1 * a04028 ^ 1)
theorem ha10601 : a10601.IsHomogeneous 337 := by
  unfold a10601
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha01311.pow 1)).mul (ha01976.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)).mul (ha04028.pow 1)))

@[irreducible]
def a10602 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a10601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10600 ^ 1)
theorem ha10602 : a10602.IsHomogeneous 337 := by
  unfold a10602
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha10601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10600.pow 1)))

@[irreducible]
def a10603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05695 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02901 ^ 1)
theorem ha10603 : a10603.IsHomogeneous 337 := by
  unfold a10603
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05695.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02901.pow 1)))

@[irreducible]
def a10604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10600 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10603 ^ 1)
theorem ha10604 : a10604.IsHomogeneous 337 := by
  unfold a10604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10603.pow 1)))

@[irreducible]
def a10605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10604 ^ 1)
theorem ha10605 : a10605.IsHomogeneous 337 := by
  unfold a10605
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10604.pow 1)))

@[irreducible]
def a10606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a07463 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00500 ^ 1 * a04028 ^ 1)
theorem ha10606 : a10606.IsHomogeneous 337 := by
  unfold a10606
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha07463.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)).mul (ha04028.pow 1)))

@[irreducible]
def a10607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10601 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10606 ^ 1)
theorem ha10607 : a10607.IsHomogeneous 337 := by
  unfold a10607
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10606.pow 1)))

@[irreducible]
def a10608 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a10607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10602 ^ 1)
theorem ha10608 : a10608.IsHomogeneous 337 := by
  unfold a10608
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha10607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10602.pow 1)))

@[irreducible]
def a10609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10608 ^ 1)
theorem ha10609 : a10609.IsHomogeneous 337 := by
  unfold a10609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10608.pow 1)))

@[irreducible]
def a10610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01304 ^ 1 * a01841 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a02889 ^ 1)
theorem ha10610 : a10610.IsHomogeneous 90 := by
  unfold a10610
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01304.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha02889.pow 1)))

@[irreducible]
def a10611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00497 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01304 ^ 1 * a01841 ^ 1)
theorem ha10611 : a10611.IsHomogeneous 96 := by
  unfold a10611
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00497.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01304.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a10612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10611 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10610 ^ 1)
theorem ha10612 : a10612.IsHomogeneous 96 := by
  unfold a10612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10611.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10610.pow 1)))

@[irreducible]
def a10613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05677 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02889 ^ 1)
theorem ha10613 : a10613.IsHomogeneous 81 := by
  unfold a10613
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05677.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02889.pow 1)))

@[irreducible]
def a10614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10610 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a10613 ^ 1)
theorem ha10614 : a10614.IsHomogeneous 90 := by
  unfold a10614
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10610.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha10613.pow 1)))

@[irreducible]
def a10615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10612 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10614 ^ 1)
theorem ha10615 : a10615.IsHomogeneous 96 := by
  unfold a10615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10612.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10614.pow 1)))

@[irreducible]
def a10616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00812 ^ 1 * a02879 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a01298 ^ 1 * a01903 ^ 1)
theorem ha10616 : a10616.IsHomogeneous 69 := by
  unfold a10616
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00812.pow 1)).mul (ha02879.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha01298.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a10617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00494 ^ 1 * a03811 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a01298 ^ 1 * a01903 ^ 1)
theorem ha10617 : a10617.IsHomogeneous 63 := by
  unfold a10617
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha01298.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a10618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10617 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a10616 ^ 1)
theorem ha10618 : a10618.IsHomogeneous 69 := by
  unfold a10618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10617.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha10616.pow 1)))

@[irreducible]
def a10619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a05662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a02879 ^ 1)
theorem ha10619 : a10619.IsHomogeneous 66 := by
  unfold a10619
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha05662.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a10620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10619 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10616 ^ 1)
theorem ha10620 : a10620.IsHomogeneous 69 := by
  unfold a10620
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10616.pow 1)))

@[irreducible]
def a10621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10618 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a10620 ^ 1)
theorem ha10621 : a10621.IsHomogeneous 69 := by
  unfold a10621
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha10620.pow 1)))

@[irreducible]
def a10622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a07132 ^ 1)
theorem ha10622 : a10622.IsHomogeneous 48 := by
  unfold a10622
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha03811.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha07132.pow 1)))

@[irreducible]
def a10623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a10622 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10617 ^ 1)
theorem ha10623 : a10623.IsHomogeneous 63 := by
  unfold a10623
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha10622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10617.pow 1)))

@[irreducible]
def a10624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10618 ^ 1)
theorem ha10624 : a10624.IsHomogeneous 69 := by
  unfold a10624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10618.pow 1)))

@[irreducible]
def a10625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10624 ^ 1)
theorem ha10625 : a10625.IsHomogeneous 69 := by
  unfold a10625
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10621.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10624.pow 1)))

@[irreducible]
def a10626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01207 ^ 1 * a01896 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a02710 ^ 1)
theorem ha10626 : a10626.IsHomogeneous 45 := by
  unfold a10626
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01207.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a03890 ^ 1)
theorem ha10627 : a10627.IsHomogeneous 45 := by
  unfold a10627
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).mul (ha01896.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a10628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10626 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10627 ^ 1)
theorem ha10628 : a10628.IsHomogeneous 51 := by
  unfold a10628
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10626.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10627.pow 1)))

@[irreducible]
def a10629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a05389 ^ 1) + (C ((54 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02710 ^ 1)
theorem ha10629 : a10629.IsHomogeneous 48 := by
  unfold a10629
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha05389.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10629 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a00003 ^ 3 * a10626 ^ 1)
theorem ha10630 : a10630.IsHomogeneous 48 := by
  unfold a10630
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10629.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha00003.pow 3)).mul (ha10626.pow 1)))

@[irreducible]
def a10631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10630 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a10628 ^ 1)
theorem ha10631 : a10631.IsHomogeneous 51 := by
  unfold a10631
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10630.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha10628.pow 1)))

@[irreducible]
def a10632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a10237 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a05389 ^ 1)
theorem ha10632 : a10632.IsHomogeneous 48 := by
  unfold a10632
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha10237.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a10633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10629 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a10632 ^ 1)
theorem ha10633 : a10633.IsHomogeneous 48 := by
  unfold a10633
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha10632.pow 1)))

@[irreducible]
def a10634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10630 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10633 ^ 1)
theorem ha10634 : a10634.IsHomogeneous 48 := by
  unfold a10634
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10630.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10633.pow 1)))

@[irreducible]
def a10635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10631 ^ 1)
theorem ha10635 : a10635.IsHomogeneous 51 := by
  unfold a10635
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10631.pow 1)))

@[irreducible]
def a10636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a07248 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a03890 ^ 1)
theorem ha10636 : a10636.IsHomogeneous 39 := by
  unfold a10636
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a10637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10627 ^ 1) + (C ((7 : ℂ) / (135 : ℂ)) * a00014 ^ 1 * a10636 ^ 1)
theorem ha10637 : a10637.IsHomogeneous 45 := by
  unfold a10637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10627.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (135 : ℂ))).mul (ha00014.pow 1)).mul (ha10636.pow 1)))

@[irreducible]
def a10638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10628 ^ 1)
theorem ha10638 : a10638.IsHomogeneous 51 := by
  unfold a10638
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10637.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10628.pow 1)))

@[irreducible]
def a10639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10631 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a10638 ^ 1)
theorem ha10639 : a10639.IsHomogeneous 51 := by
  unfold a10639
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10631.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha10638.pow 1)))

@[irreducible]
def a10640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10635 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10639 ^ 1)
theorem ha10640 : a10640.IsHomogeneous 51 := by
  unfold a10640
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10635.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10639.pow 1)))

@[irreducible]
def a10641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a05662 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00127 ^ 1 * a10640 ^ 1)
theorem ha10641 : a10641.IsHomogeneous 69 := by
  unfold a10641
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha05662.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00127.pow 1)).mul (ha10640.pow 1)))

@[irreducible]
def a10642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10619 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10641 ^ 1)
theorem ha10642 : a10642.IsHomogeneous 69 := by
  unfold a10642
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10641.pow 1)))

@[irreducible]
def a10643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10642 ^ 1)
theorem ha10643 : a10643.IsHomogeneous 69 := by
  unfold a10643
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10642.pow 1)))

@[irreducible]
def a10644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10621 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a10643 ^ 1)
theorem ha10644 : a10644.IsHomogeneous 69 := by
  unfold a10644
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10621.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha10643.pow 1)))

@[irreducible]
def a10645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10625 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10644 ^ 1)
theorem ha10645 : a10645.IsHomogeneous 69 := by
  unfold a10645
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10625.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10644.pow 1)))

@[irreducible]
def a10646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01228 ^ 1 * a01962 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00841 ^ 1 * a02754 ^ 1)
theorem ha10646 : a10646.IsHomogeneous 75 := by
  unfold a10646
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01228.pow 1)).mul (ha01962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00841.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a10647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a04004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01228 ^ 1 * a01962 ^ 1)
theorem ha10647 : a10647.IsHomogeneous 72 := by
  unfold a10647
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha04004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01228.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a10648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10647 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10646 ^ 1)
theorem ha10648 : a10648.IsHomogeneous 75 := by
  unfold a10648
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10647.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10646.pow 1)))

@[irreducible]
def a10649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a00298 ^ 1 * a03811 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a02754 ^ 1)
theorem ha10649 : a10649.IsHomogeneous 75 := by
  unfold a10649
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a10650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10646 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a10649 ^ 1)
theorem ha10650 : a10650.IsHomogeneous 75 := by
  unfold a10650
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha10649.pow 1)))

@[irreducible]
def a10651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10648 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10650 ^ 1)
theorem ha10651 : a10651.IsHomogeneous 75 := by
  unfold a10651
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10648.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10650.pow 1)))

@[irreducible]
def a10652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a07416 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10649 ^ 1)
theorem ha10652 : a10652.IsHomogeneous 75 := by
  unfold a10652
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha07416.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10649.pow 1)))

@[irreducible]
def a10653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10650 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a10652 ^ 1)
theorem ha10653 : a10653.IsHomogeneous 75 := by
  unfold a10653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10650.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha10652.pow 1)))

@[irreducible]
def a10654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10653 ^ 1)
theorem ha10654 : a10654.IsHomogeneous 75 := by
  unfold a10654
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10653.pow 1)))

@[irreducible]
def a10655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a04004 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a07425 ^ 1)
theorem ha10655 : a10655.IsHomogeneous 75 := by
  unfold a10655
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha04004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha07425.pow 1)))

@[irreducible]
def a10656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10647 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10655 ^ 1)
theorem ha10656 : a10656.IsHomogeneous 75 := by
  unfold a10656
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10647.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10655.pow 1)))

@[irreducible]
def a10657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10648 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10656 ^ 1)
theorem ha10657 : a10657.IsHomogeneous 75 := by
  unfold a10657
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10648.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10656.pow 1)))

@[irreducible]
def a10658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10657 ^ 1)
theorem ha10658 : a10658.IsHomogeneous 75 := by
  unfold a10658
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10657.pow 1)))

@[irreducible]
def a10659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10658 ^ 1)
theorem ha10659 : a10659.IsHomogeneous 75 := by
  unfold a10659
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10658.pow 1)))

@[irreducible]
def a10660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a10645 ^ 1) + (C ((72 : ℂ) / (1 : ℂ)) * a10659 ^ 1)
theorem ha10660 : a10660.IsHomogeneous 75 := by
  unfold a10660
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha10645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (1 : ℂ))).mul (ha10659.pow 1)))

@[irreducible]
def a10661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05677 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a10660 ^ 1)
theorem ha10661 : a10661.IsHomogeneous 81 := by
  unfold a10661
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05677.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha10660.pow 1)))

@[irreducible]
def a10662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10661 ^ 1)
theorem ha10662 : a10662.IsHomogeneous 87 := by
  unfold a10662
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10613.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10661.pow 1)))

@[irreducible]
def a10663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10614 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10662 ^ 1)
theorem ha10663 : a10663.IsHomogeneous 93 := by
  unfold a10663
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10614.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10662.pow 1)))

@[irreducible]
def a10664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10615 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10663 ^ 1)
theorem ha10664 : a10664.IsHomogeneous 99 := by
  unfold a10664
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10615.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10663.pow 1)))

@[irreducible]
def a10665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00152 ^ 1 * a07120 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00497 ^ 1 * a03803 ^ 1)
theorem ha10665 : a10665.IsHomogeneous 102 := by
  unfold a10665
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00152.pow 1)).mul (ha07120.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00497.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a10666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10665 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10611 ^ 1)
theorem ha10666 : a10666.IsHomogeneous 102 := by
  unfold a10666
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10665.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10611.pow 1)))

@[irreducible]
def a10667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10666 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10612 ^ 1)
theorem ha10667 : a10667.IsHomogeneous 102 := by
  unfold a10667
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10666.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10612.pow 1)))

@[irreducible]
def a10668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10667 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10615 ^ 1)
theorem ha10668 : a10668.IsHomogeneous 102 := by
  unfold a10668
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10667.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10615.pow 1)))

@[irreducible]
def a10669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10668 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10664 ^ 1)
theorem ha10669 : a10669.IsHomogeneous 105 := by
  unfold a10669
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10668.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10664.pow 1)))

@[irreducible]
def a10670 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00850 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01275 ^ 1 * a01979 ^ 1)
theorem ha10670 : a10670.IsHomogeneous 295 := by
  unfold a10670
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01275.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a10671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a04032 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a01275 ^ 1 * a01979 ^ 1)
theorem ha10671 : a10671.IsHomogeneous 331 := by
  unfold a10671
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha04032.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha01275.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a10672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10671 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a10670 ^ 1)
theorem ha10672 : a10672.IsHomogeneous 331 := by
  unfold a10672
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10671.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha10670.pow 1)))

@[irreducible]
def a10673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a05595 ^ 1)
theorem ha10673 : a10673.IsHomogeneous 257 := by
  unfold a10673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha02837.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a10674 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10670 ^ 1)
theorem ha10674 : a10674.IsHomogeneous 295 := by
  unfold a10674
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10670.pow 1)))

@[irreducible]
def a10675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10672 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a10674 ^ 1)
theorem ha10675 : a10675.IsHomogeneous 331 := by
  unfold a10675
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10672.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha10674.pow 1)))

@[irreducible]
def a10676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a05595 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a10542 ^ 1)
theorem ha10676 : a10676.IsHomogeneous 191 := by
  unfold a10676
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha05595.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha10542.pow 1)))

@[irreducible]
def a10677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10673 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a10676 ^ 1)
theorem ha10677 : a10677.IsHomogeneous 257 := by
  unfold a10677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10673.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha10676.pow 1)))

@[irreducible]
def a10678 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10677 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10674 ^ 1)
theorem ha10678 : a10678.IsHomogeneous 295 := by
  unfold a10678
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10677.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10674.pow 1)))

@[irreducible]
def a10679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10675 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a10678 ^ 1)
theorem ha10679 : a10679.IsHomogeneous 331 := by
  unfold a10679
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10675.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha10678.pow 1)))

@[irreducible]
def a10680 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a04032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a07468 ^ 1)
theorem ha10680 : a10680.IsHomogeneous 331 := by
  unfold a10680
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha04032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha07468.pow 1)))

@[irreducible]
def a10681 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a10680 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10671 ^ 1)
theorem ha10681 : a10681.IsHomogeneous 331 := by
  unfold a10681
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha10680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10671.pow 1)))

@[irreducible]
def a10682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10681 ^ 1)
theorem ha10682 : a10682.IsHomogeneous 331 := by
  unfold a10682
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10681.pow 1)))

@[irreducible]
def a10683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10675 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10682 ^ 1)
theorem ha10683 : a10683.IsHomogeneous 331 := by
  unfold a10683
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10675.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10682.pow 1)))

@[irreducible]
def a10684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10679 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10683 ^ 1)
theorem ha10684 : a10684.IsHomogeneous 331 := by
  unfold a10684
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10683.pow 1)))

@[irreducible]
def a10685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a10684 ^ 1) + (C ((1 : ℂ) / (34992 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 6 * a10669 ^ 1)
theorem ha10685 : a10685.IsHomogeneous 337 := by
  unfold a10685
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha10684.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (34992 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 6)).mul (ha10669.pow 1)))

@[irreducible]
def a10686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05695 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a10685 ^ 1)
theorem ha10686 : a10686.IsHomogeneous 337 := by
  unfold a10686
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha10685.pow 1)))

@[irreducible]
def a10687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10603 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10686 ^ 1)
theorem ha10687 : a10687.IsHomogeneous 337 := by
  unfold a10687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10603.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10686.pow 1)))

@[irreducible]
def a10688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10604 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10687 ^ 1)
theorem ha10688 : a10688.IsHomogeneous 337 := by
  unfold a10688
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10604.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10687.pow 1)))

@[irreducible]
def a10689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10688 ^ 1)
theorem ha10689 : a10689.IsHomogeneous 337 := by
  unfold a10689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10688.pow 1)))

@[irreducible]
def a10690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10689 ^ 1)
theorem ha10690 : a10690.IsHomogeneous 337 := by
  unfold a10690
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10689.pow 1)))

@[irreducible]
def a10691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a05699 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a10690 ^ 1)
theorem ha10691 : a10691.IsHomogeneous 763 := by
  unfold a10691
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha05699.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha10690.pow 1)))

@[irreducible]
def a10692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10593 ^ 1)
theorem ha10692 : a10692.IsHomogeneous 1096 := by
  unfold a10692
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10691.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10593.pow 1)))

@[irreducible]
def a10693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10594 ^ 1)
theorem ha10693 : a10693.IsHomogeneous 1429 := by
  unfold a10693
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10692.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10594.pow 1)))

@[irreducible]
def a10694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10693 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10595 ^ 1)
theorem ha10694 : a10694.IsHomogeneous 1762 := by
  unfold a10694
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10693.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10595.pow 1)))

@[irreducible]
def a10695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10599 ^ 1)
theorem ha10695 : a10695.IsHomogeneous 2095 := by
  unfold a10695
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10599.pow 1)))

@[irreducible]
def a10696 : Poly := (C ((-64 : ℂ) / (729 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 6 * a10695 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a10589 ^ 1) + (C ((-1 : ℂ) / (27 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 6 * a10202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a10187 ^ 1)
theorem ha10696 : a10696.IsHomogeneous 2261 := by
  unfold a10696
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-64 : ℂ) / (729 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha10695.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha10589.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha10202.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha10187.pow 1)))

@[irreducible]
def a10697 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01983 ^ 1 * a02043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00881 ^ 1 * a04037 ^ 1)
theorem ha10697 : a10697.IsHomogeneous 2031 := by
  unfold a10697
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01983.pow 1)).mul (ha02043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00881.pow 1)).mul (ha04037.pow 1)))

@[irreducible]
def a10698 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00853 ^ 1 * a04151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01983 ^ 1 * a02043 ^ 1)
theorem ha10698 : a10698.IsHomogeneous 1734 := by
  unfold a10698
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00853.pow 1)).mul (ha04151.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01983.pow 1)).mul (ha02043.pow 1)))

@[irreducible]
def a10699 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10698 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10697 ^ 1)
theorem ha10699 : a10699.IsHomogeneous 2091 := by
  unfold a10699
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10698.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10697.pow 1)))

@[irreducible]
def a10700 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a04037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a07474 ^ 1)
theorem ha10700 : a10700.IsHomogeneous 2328 := by
  unfold a10700
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha04037.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha07474.pow 1)))

@[irreducible]
def a10701 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10700 ^ 1)
theorem ha10701 : a10701.IsHomogeneous 2388 := by
  unfold a10701
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10697.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10700.pow 1)))

@[irreducible]
def a10702 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10699 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10701 ^ 1)
theorem ha10702 : a10702.IsHomogeneous 2448 := by
  unfold a10702
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10699.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10701.pow 1)))

@[irreducible]
def a10703 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00312 ^ 1 * a07667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00853 ^ 1 * a04151 ^ 1)
theorem ha10703 : a10703.IsHomogeneous 1437 := by
  unfold a10703
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00312.pow 1)).mul (ha07667.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00853.pow 1)).mul (ha04151.pow 1)))

@[irreducible]
def a10704 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10698 ^ 1)
theorem ha10704 : a10704.IsHomogeneous 1794 := by
  unfold a10704
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10703.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10698.pow 1)))

@[irreducible]
def a10705 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10704 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10699 ^ 1)
theorem ha10705 : a10705.IsHomogeneous 2151 := by
  unfold a10705
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10704.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10699.pow 1)))

@[irreducible]
def a10706 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10702 ^ 1)
theorem ha10706 : a10706.IsHomogeneous 2508 := by
  unfold a10706
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10702.pow 1)))

@[irreducible]
def a10707 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01886 ^ 1 * a01949 ^ 1)
theorem ha10707 : a10707.IsHomogeneous 1755 := by
  unfold a10707
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01886.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a10708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a03978 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01886 ^ 1 * a01949 ^ 1)
theorem ha10708 : a10708.IsHomogeneous 1482 := by
  unfold a10708
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha03978.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01886.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a10709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10708 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10707 ^ 1)
theorem ha10709 : a10709.IsHomogeneous 1815 := by
  unfold a10709
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10708.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10707.pow 1)))

@[irreducible]
def a10710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a03873 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a07222 ^ 1)
theorem ha10710 : a10710.IsHomogeneous 2028 := by
  unfold a10710
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha03873.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a10711 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10707 ^ 1)
theorem ha10711 : a10711.IsHomogeneous 2088 := by
  unfold a10711
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10710.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10707.pow 1)))

@[irreducible]
def a10712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10709 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10711 ^ 1)
theorem ha10712 : a10712.IsHomogeneous 2148 := by
  unfold a10712
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10709.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10711.pow 1)))

@[irreducible]
def a10713 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a03978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a07382 ^ 1)
theorem ha10713 : a10713.IsHomogeneous 1209 := by
  unfold a10713
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha03978.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha07382.pow 1)))

@[irreducible]
def a10714 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10708 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10713 ^ 1)
theorem ha10714 : a10714.IsHomogeneous 1542 := by
  unfold a10714
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10708.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10713.pow 1)))

@[irreducible]
def a10715 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10714 ^ 1)
theorem ha10715 : a10715.IsHomogeneous 1875 := by
  unfold a10715
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10709.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10714.pow 1)))

@[irreducible]
def a10716 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10715 ^ 1)
theorem ha10716 : a10716.IsHomogeneous 2208 := by
  unfold a10716
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10712.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10715.pow 1)))

@[irreducible]
def a10717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00802 ^ 1 * a03569 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a01707 ^ 1 * a01883 ^ 1)
theorem ha10717 : a10717.IsHomogeneous 1243 := by
  unfold a10717
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00802.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha01707.pow 1)).mul (ha01883.pow 1)))

@[irreducible]
def a10718 : Poly := (C ((-192 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a03869 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01707 ^ 1 * a01883 ^ 1)
theorem ha10718 : a10718.IsHomogeneous 1418 := by
  unfold a10718
  exact (((((isHomogeneous_C (σ := Fin 6) ((-192 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha03869.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01707.pow 1)).mul (ha01883.pow 1)))

@[irreducible]
def a10719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10717 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a10718 ^ 1)
theorem ha10719 : a10719.IsHomogeneous 1497 := by
  unfold a10719
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha10718.pow 1)))

@[irreducible]
def a10720 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00802 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00295 ^ 1 * a06734 ^ 1)
theorem ha10720 : a10720.IsHomogeneous 1068 := by
  unfold a10720
  exact (((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00802.pow 1)).mul (ha03569.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00295.pow 1)).mul (ha06734.pow 1)))

@[irreducible]
def a10721 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10720 ^ 1)
theorem ha10721 : a10721.IsHomogeneous 1322 := by
  unfold a10721
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10717.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10720.pow 1)))

@[irreducible]
def a10722 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10721 ^ 1)
theorem ha10722 : a10722.IsHomogeneous 1576 := by
  unfold a10722
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10719.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10721.pow 1)))

@[irreducible]
def a10723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a03869 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a07217 ^ 1)
theorem ha10723 : a10723.IsHomogeneous 1593 := by
  unfold a10723
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha03869.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha07217.pow 1)))

@[irreducible]
def a10724 : Poly := (C ((-192 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10723 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10718 ^ 1)
theorem ha10724 : a10724.IsHomogeneous 1672 := by
  unfold a10724
  exact ((((isHomogeneous_C (σ := Fin 6) ((-192 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10723.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10718.pow 1)))

@[irreducible]
def a10725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10719 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a10724 ^ 1)
theorem ha10725 : a10725.IsHomogeneous 1751 := by
  unfold a10725
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10719.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha10724.pow 1)))

@[irreducible]
def a10726 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10722 ^ 1)
theorem ha10726 : a10726.IsHomogeneous 1830 := by
  unfold a10726
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10725.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10722.pow 1)))

@[irreducible]
def a10727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01705 ^ 1 * a02922 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01320 ^ 1 * a03566 ^ 1)
theorem ha10727 : a10727.IsHomogeneous 430 := by
  unfold a10727
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01705.pow 1)).mul (ha02922.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01320.pow 1)).mul (ha03566.pow 1)))

@[irreducible]
def a10728 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1 * a02922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a05735 ^ 1)
theorem ha10728 : a10728.IsHomogeneous 510 := by
  unfold a10728
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).mul (ha02922.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha05735.pow 1)))

@[irreducible]
def a10729 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10728 ^ 1)
theorem ha10729 : a10729.IsHomogeneous 510 := by
  unfold a10729
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10728.pow 1)))

@[irreducible]
def a10730 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a06730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01320 ^ 1 * a03566 ^ 1)
theorem ha10730 : a10730.IsHomogeneous 350 := by
  unfold a10730
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha06730.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01320.pow 1)).mul (ha03566.pow 1)))

@[irreducible]
def a10731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10727 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10730 ^ 1)
theorem ha10731 : a10731.IsHomogeneous 430 := by
  unfold a10731
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10727.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10730.pow 1)))

@[irreducible]
def a10732 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10729 ^ 1)
theorem ha10732 : a10732.IsHomogeneous 510 := by
  unfold a10732
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10729.pow 1)))

@[irreducible]
def a10733 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a03566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01705 ^ 1 * a02920 ^ 1)
theorem ha10733 : a10733.IsHomogeneous 345 := by
  unfold a10733
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha03566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01705.pow 1)).mul (ha02920.pow 1)))

@[irreducible]
def a10734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a05732 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1 * a02920 ^ 1)
theorem ha10734 : a10734.IsHomogeneous 425 := by
  unfold a10734
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha05732.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).mul (ha02920.pow 1)))

@[irreducible]
def a10735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10734 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10733 ^ 1)
theorem ha10735 : a10735.IsHomogeneous 425 := by
  unfold a10735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10734.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10733.pow 1)))

@[irreducible]
def a10736 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a06730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a03566 ^ 1)
theorem ha10736 : a10736.IsHomogeneous 265 := by
  unfold a10736
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha06730.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha03566.pow 1)))

@[irreducible]
def a10737 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10733 ^ 1)
theorem ha10737 : a10737.IsHomogeneous 345 := by
  unfold a10737
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10733.pow 1)))

@[irreducible]
def a10738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10735 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10737 ^ 1)
theorem ha10738 : a10738.IsHomogeneous 425 := by
  unfold a10738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10735.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10737.pow 1)))

@[irreducible]
def a10739 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a03566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01705 ^ 1)
theorem ha10739 : a10739.IsHomogeneous 260 := by
  unfold a10739
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha03566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01705.pow 1)))

@[irreducible]
def a10740 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a05730 ^ 1)
theorem ha10740 : a10740.IsHomogeneous 340 := by
  unfold a10740
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha05730.pow 1)))

@[irreducible]
def a10741 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a10739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10740 ^ 1)
theorem ha10741 : a10741.IsHomogeneous 340 := by
  unfold a10741
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha10739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10740.pow 1)))

@[irreducible]
def a10742 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00714 ^ 1)
theorem ha10742 : a10742.IsHomogeneous 255 := by
  unfold a10742
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00714.pow 1)))

@[irreducible]
def a10743 : Poly := (C ((-5 : ℂ) / (384 : ℂ)) * a00714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 2)
theorem ha10743 : a10743.IsHomogeneous 170 := by
  unfold a10743
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (384 : ℂ))).mul (ha00714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a10744 : Poly := (C ((-384 : ℂ) / (5 : ℂ)) * a10743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1)
theorem ha10744 : a10744.IsHomogeneous 170 := by
  unfold a10744
  exact (((isHomogeneous_C (σ := Fin 6) ((-384 : ℂ) / (5 : ℂ))).mul (ha10743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)))

@[irreducible]
def a10745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a10744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10742 ^ 1)
theorem ha10745 : a10745.IsHomogeneous 255 := by
  unfold a10745
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha10744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10742.pow 1)))

@[irreducible]
def a10746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a10745 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a05730 ^ 1)
theorem ha10746 : a10746.IsHomogeneous 340 := by
  unfold a10746
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha10745.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha05730.pow 1)))

@[irreducible]
def a10747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10740 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10746 ^ 1)
theorem ha10747 : a10747.IsHomogeneous 340 := by
  unfold a10747
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10746.pow 1)))

@[irreducible]
def a10748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10741 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10747 ^ 1)
theorem ha10748 : a10748.IsHomogeneous 340 := by
  unfold a10748
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10741.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10747.pow 1)))

@[irreducible]
def a10749 : Poly := (C ((-1 : ℂ) / (64 : ℂ)) * a00714 ^ 1 * a05732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a10748 ^ 1)
theorem ha10749 : a10749.IsHomogeneous 425 := by
  unfold a10749
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (64 : ℂ))).mul (ha00714.pow 1)).mul (ha05732.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha10748.pow 1)))

@[irreducible]
def a10750 : Poly := (C ((-64 : ℂ) / (1 : ℂ)) * a10749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10734 ^ 1)
theorem ha10750 : a10750.IsHomogeneous 425 := by
  unfold a10750
  exact (((isHomogeneous_C (σ := Fin 6) ((-64 : ℂ) / (1 : ℂ))).mul (ha10749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10734.pow 1)))

@[irreducible]
def a10751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10750 ^ 1)
theorem ha10751 : a10751.IsHomogeneous 425 := by
  unfold a10751
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10750.pow 1)))

end CycleQ2Concrete
