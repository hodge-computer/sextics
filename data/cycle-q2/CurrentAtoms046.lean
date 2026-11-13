import Proposal.CurrentAtoms045

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a13568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13538 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a13563 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a13567 ^ 1)
theorem ha13568 : a13568.IsHomogeneous 39 := by
  unfold a13568
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha13563.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha13567.pow 1)))

@[irreducible]
def a13569 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1)
theorem ha13569 : a13569.IsHomogeneous 36 := by
  unfold a13569
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a13570 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a13545 ^ 1) + (C ((-1 : ℂ) / (12 : ℂ)) * a13569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13560 ^ 1)
theorem ha13570 : a13570.IsHomogeneous 36 := by
  unfold a13570
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha13545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha13569.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13560.pow 1)))

@[irreducible]
def a13571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13561 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a13570 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a13546 ^ 1)
theorem ha13571 : a13571.IsHomogeneous 36 := by
  unfold a13571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha13570.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha13546.pow 1)))

@[irreducible]
def a13572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13571 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a00003 ^ 3 * a13547 ^ 1)
theorem ha13572 : a13572.IsHomogeneous 36 := by
  unfold a13572
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13571.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha00003.pow 3)).mul (ha13547.pow 1)))

@[irreducible]
def a13573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13563 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a13548 ^ 1)
theorem ha13573 : a13573.IsHomogeneous 39 := by
  unfold a13573
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13563.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha13548.pow 1)))

@[irreducible]
def a13574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13568 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a13573 ^ 1)
theorem ha13574 : a13574.IsHomogeneous 39 := by
  unfold a13574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13568.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha13573.pow 1)))

@[irreducible]
def a13575 : Poly := (C ((-14 : ℂ) / (9 : ℂ)) * a13518 ^ 1) + (C ((-7 : ℂ) / (27 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a13574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13425 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13462 ^ 1)
theorem ha13575 : a13575.IsHomogeneous 54 := by
  unfold a13575
  exact (((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (9 : ℂ))).mul (ha13518.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (27 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha13574.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13425.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13462.pow 1)))

@[irreducible]
def a13576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07634 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13575 ^ 1)
theorem ha13576 : a13576.IsHomogeneous 96 := by
  unfold a13576
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07634.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13575.pow 1)))

@[irreducible]
def a13577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13364 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13576 ^ 1)
theorem ha13577 : a13577.IsHomogeneous 138 := by
  unfold a13577
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13364.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13576.pow 1)))

@[irreducible]
def a13578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13365 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13577 ^ 1)
theorem ha13578 : a13578.IsHomogeneous 183 := by
  unfold a13578
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13365.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13577.pow 1)))

@[irreducible]
def a13579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13366 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13578 ^ 1)
theorem ha13579 : a13579.IsHomogeneous 225 := by
  unfold a13579
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13366.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13578.pow 1)))

@[irreducible]
def a13580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13370 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13579 ^ 1)
theorem ha13580 : a13580.IsHomogeneous 267 := by
  unfold a13580
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13370.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13579.pow 1)))

@[irreducible]
def a13581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01702 ^ 1 * a04141 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02036 ^ 1 * a03562 ^ 1)
theorem ha13581 : a13581.IsHomogeneous 177 := by
  unfold a13581
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01702.pow 1)).mul (ha04141.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02036.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a13582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02036 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a06725 ^ 1)
theorem ha13582 : a13582.IsHomogeneous 135 := by
  unfold a13582
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02036.pow 1)).mul (ha03562.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13581 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13582 ^ 1)
theorem ha13583 : a13583.IsHomogeneous 177 := by
  unfold a13583
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13581.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13582.pow 1)))

@[irreducible]
def a13584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a07654 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a01702 ^ 1 * a04141 ^ 1)
theorem ha13584 : a13584.IsHomogeneous 213 := by
  unfold a13584
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha07654.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)).mul (ha04141.pow 1)))

@[irreducible]
def a13585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13584 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13581 ^ 1)
theorem ha13585 : a13585.IsHomogeneous 213 := by
  unfold a13585
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13584.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13581.pow 1)))

@[irreducible]
def a13586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13585 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13583 ^ 1)
theorem ha13586 : a13586.IsHomogeneous 213 := by
  unfold a13586
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13585.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13583.pow 1)))

@[irreducible]
def a13587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a06725 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a12210 ^ 1)
theorem ha13587 : a13587.IsHomogeneous 90 := by
  unfold a13587
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha06725.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha12210.pow 1)))

@[irreducible]
def a13588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13582 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13587 ^ 1)
theorem ha13588 : a13588.IsHomogeneous 135 := by
  unfold a13588
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13582.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13587.pow 1)))

@[irreducible]
def a13589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13583 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13588 ^ 1)
theorem ha13589 : a13589.IsHomogeneous 177 := by
  unfold a13589
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13583.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13588.pow 1)))

@[irreducible]
def a13590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13586 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13589 ^ 1)
theorem ha13590 : a13590.IsHomogeneous 213 := by
  unfold a13590
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13586.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13589.pow 1)))

@[irreducible]
def a13591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01702 ^ 1 * a04139 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a03562 ^ 1)
theorem ha13591 : a13591.IsHomogeneous 135 := by
  unfold a13591
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01702.pow 1)).mul (ha04139.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a13592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a06725 ^ 1)
theorem ha13592 : a13592.IsHomogeneous 93 := by
  unfold a13592
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03562.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13591 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13592 ^ 1)
theorem ha13593 : a13593.IsHomogeneous 135 := by
  unfold a13593
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13591.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13592.pow 1)))

@[irreducible]
def a13594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a07651 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a01702 ^ 1 * a04139 ^ 1)
theorem ha13594 : a13594.IsHomogeneous 171 := by
  unfold a13594
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha07651.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)).mul (ha04139.pow 1)))

@[irreducible]
def a13595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13594 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13591 ^ 1)
theorem ha13595 : a13595.IsHomogeneous 171 := by
  unfold a13595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13594.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13591.pow 1)))

@[irreducible]
def a13596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13595 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13593 ^ 1)
theorem ha13596 : a13596.IsHomogeneous 171 := by
  unfold a13596
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13593.pow 1)))

@[irreducible]
def a13597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03562 ^ 1)
theorem ha13597 : a13597.IsHomogeneous 93 := by
  unfold a13597
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a13598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a07649 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a01702 ^ 1)
theorem ha13598 : a13598.IsHomogeneous 129 := by
  unfold a13598
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha07649.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a13599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13598 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13597 ^ 1)
theorem ha13599 : a13599.IsHomogeneous 129 := by
  unfold a13599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13598.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13597.pow 1)))

@[irreducible]
def a13600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a01702 ^ 1)
theorem ha13600 : a13600.IsHomogeneous 87 := by
  unfold a13600
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a13601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha13601 : a13601.IsHomogeneous 84 := by
  unfold a13601
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a13602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13601 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha13602 : a13602.IsHomogeneous 84 := by
  unfold a13602
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13601.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a13603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13602 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13600 ^ 1)
theorem ha13603 : a13603.IsHomogeneous 126 := by
  unfold a13603
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13602.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13600.pow 1)))

@[irreducible]
def a13604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13603 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a07649 ^ 1)
theorem ha13604 : a13604.IsHomogeneous 168 := by
  unfold a13604
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13603.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha07649.pow 1)))

@[irreducible]
def a13605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13604 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13598 ^ 1)
theorem ha13605 : a13605.IsHomogeneous 168 := by
  unfold a13605
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13604.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13598.pow 1)))

@[irreducible]
def a13606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13605 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13599 ^ 1)
theorem ha13606 : a13606.IsHomogeneous 168 := by
  unfold a13606
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13605.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13599.pow 1)))

@[irreducible]
def a13607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13606 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a07651 ^ 1)
theorem ha13607 : a13607.IsHomogeneous 210 := by
  unfold a13607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13606.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha07651.pow 1)))

@[irreducible]
def a13608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13607 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13594 ^ 1)
theorem ha13608 : a13608.IsHomogeneous 210 := by
  unfold a13608
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13607.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13594.pow 1)))

@[irreducible]
def a13609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13608 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13595 ^ 1)
theorem ha13609 : a13609.IsHomogeneous 210 := by
  unfold a13609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13608.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13595.pow 1)))

@[irreducible]
def a13610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13609 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13596 ^ 1)
theorem ha13610 : a13610.IsHomogeneous 210 := by
  unfold a13610
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13609.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13596.pow 1)))

@[irreducible]
def a13611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13610 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a07654 ^ 1)
theorem ha13611 : a13611.IsHomogeneous 252 := by
  unfold a13611
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13610.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha07654.pow 1)))

@[irreducible]
def a13612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13611 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13584 ^ 1)
theorem ha13612 : a13612.IsHomogeneous 252 := by
  unfold a13612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13611.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13584.pow 1)))

@[irreducible]
def a13613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13612 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13585 ^ 1)
theorem ha13613 : a13613.IsHomogeneous 252 := by
  unfold a13613
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13612.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13585.pow 1)))

@[irreducible]
def a13614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13613 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13586 ^ 1)
theorem ha13614 : a13614.IsHomogeneous 252 := by
  unfold a13614
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13613.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13586.pow 1)))

@[irreducible]
def a13615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13614 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13590 ^ 1)
theorem ha13615 : a13615.IsHomogeneous 252 := by
  unfold a13615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13614.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13590.pow 1)))

@[irreducible]
def a13616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13615 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00326 ^ 1 * a07658 ^ 1)
theorem ha13616 : a13616.IsHomogeneous 312 := by
  unfold a13616
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13615.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00326.pow 1)).mul (ha07658.pow 1)))

@[irreducible]
def a13617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13616 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13367 ^ 1)
theorem ha13617 : a13617.IsHomogeneous 312 := by
  unfold a13617
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13616.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13367.pow 1)))

@[irreducible]
def a13618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13617 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13368 ^ 1)
theorem ha13618 : a13618.IsHomogeneous 312 := by
  unfold a13618
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13617.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13368.pow 1)))

@[irreducible]
def a13619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13618 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13369 ^ 1)
theorem ha13619 : a13619.IsHomogeneous 312 := by
  unfold a13619
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13618.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13369.pow 1)))

@[irreducible]
def a13620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13619 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13370 ^ 1)
theorem ha13620 : a13620.IsHomogeneous 312 := by
  unfold a13620
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13619.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13370.pow 1)))

@[irreducible]
def a13621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13620 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13580 ^ 1)
theorem ha13621 : a13621.IsHomogeneous 312 := by
  unfold a13621
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13620.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13580.pow 1)))

@[irreducible]
def a13622 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07663 ^ 1)
theorem ha13622 : a13622.IsHomogeneous 372 := by
  unfold a13622
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07663.pow 1)))

@[irreducible]
def a13623 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13622 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13334 ^ 1)
theorem ha13623 : a13623.IsHomogeneous 432 := by
  unfold a13623
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13334.pow 1)))

@[irreducible]
def a13624 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13335 ^ 1)
theorem ha13624 : a13624.IsHomogeneous 492 := by
  unfold a13624
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13335.pow 1)))

@[irreducible]
def a13625 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13624 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13336 ^ 1)
theorem ha13625 : a13625.IsHomogeneous 552 := by
  unfold a13625
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13624.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13336.pow 1)))

@[irreducible]
def a13626 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13625 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13360 ^ 1)
theorem ha13626 : a13626.IsHomogeneous 612 := by
  unfold a13626
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13625.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13360.pow 1)))

@[irreducible]
def a13627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1 * a07667 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a13626 ^ 1)
theorem ha13627 : a13627.IsHomogeneous 1110 := by
  unfold a13627
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).mul (ha07667.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha13626.pow 1)))

@[irreducible]
def a13628 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a13627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10703 ^ 1)
theorem ha13628 : a13628.IsHomogeneous 1497 := by
  unfold a13628
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha13627.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10703.pow 1)))

@[irreducible]
def a13629 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13628 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10704 ^ 1)
theorem ha13629 : a13629.IsHomogeneous 1854 := by
  unfold a13629
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13628.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10704.pow 1)))

@[irreducible]
def a13630 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13629 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10705 ^ 1)
theorem ha13630 : a13630.IsHomogeneous 2211 := by
  unfold a13630
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13629.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10705.pow 1)))

@[irreducible]
def a13631 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13630 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a10706 ^ 1)
theorem ha13631 : a13631.IsHomogeneous 2568 := by
  unfold a13631
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13630.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha10706.pow 1)))

@[irreducible]
def a13632 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13330 ^ 1)
theorem ha13632 : a13632.IsHomogeneous 2925 := by
  unfold a13632
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13631.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13330.pow 1)))

@[irreducible]
def a13633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a04155 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02046 ^ 1 * a02104 ^ 1)
theorem ha13633 : a13633.IsHomogeneous 2152 := by
  unfold a13633
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha04155.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02046.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a13634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02046 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a04232 ^ 1)
theorem ha13634 : a13634.IsHomogeneous 1735 := by
  unfold a13634
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02046.pow 1)).mul (ha02104.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a13635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13633 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13634 ^ 1)
theorem ha13635 : a13635.IsHomogeneous 2152 := by
  unfold a13635
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13633.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13634.pow 1)))

@[irreducible]
def a13636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a04232 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a07779 ^ 1)
theorem ha13636 : a13636.IsHomogeneous 1318 := by
  unfold a13636
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha04232.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha07779.pow 1)))

@[irreducible]
def a13637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13634 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13636 ^ 1)
theorem ha13637 : a13637.IsHomogeneous 1735 := by
  unfold a13637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13634.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13636.pow 1)))

@[irreducible]
def a13638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13635 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13637 ^ 1)
theorem ha13638 : a13638.IsHomogeneous 2152 := by
  unfold a13638
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13635.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13637.pow 1)))

@[irreducible]
def a13639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00930 ^ 1 * a04144 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02038 ^ 1 * a02102 ^ 1)
theorem ha13639 : a13639.IsHomogeneous 313 := by
  unfold a13639
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00930.pow 1)).mul (ha04144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02038.pow 1)).mul (ha02102.pow 1)))

@[irreducible]
def a13640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a04229 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02038 ^ 1 * a02102 ^ 1)
theorem ha13640 : a13640.IsHomogeneous 313 := by
  unfold a13640
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha04229.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02038.pow 1)).mul (ha02102.pow 1)))

@[irreducible]
def a13641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13639 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13640 ^ 1)
theorem ha13641 : a13641.IsHomogeneous 313 := by
  unfold a13641
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13640.pow 1)))

@[irreducible]
def a13642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07775 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00878 ^ 1 * a04229 ^ 1)
theorem ha13642 : a13642.IsHomogeneous 313 := by
  unfold a13642
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00878.pow 1)).mul (ha04229.pow 1)))

@[irreducible]
def a13643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13640 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13642 ^ 1)
theorem ha13643 : a13643.IsHomogeneous 313 := by
  unfold a13643
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13640.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13642.pow 1)))

@[irreducible]
def a13644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13641 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13643 ^ 1)
theorem ha13644 : a13644.IsHomogeneous 313 := by
  unfold a13644
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13641.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13643.pow 1)))

@[irreducible]
def a13645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07658 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00930 ^ 1 * a04144 ^ 1)
theorem ha13645 : a13645.IsHomogeneous 313 := by
  unfold a13645
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07658.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00930.pow 1)).mul (ha04144.pow 1)))

@[irreducible]
def a13646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13639 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a13645 ^ 1)
theorem ha13646 : a13646.IsHomogeneous 313 := by
  unfold a13646
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha13645.pow 1)))

@[irreducible]
def a13647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13641 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13646 ^ 1)
theorem ha13647 : a13647.IsHomogeneous 313 := by
  unfold a13647
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13641.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13646.pow 1)))

@[irreducible]
def a13648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13644 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13647 ^ 1)
theorem ha13648 : a13648.IsHomogeneous 313 := by
  unfold a13648
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13647.pow 1)))

@[irreducible]
def a13649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a01207 ^ 1)
theorem ha13649 : a13649.IsHomogeneous 39 := by
  unfold a13649
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a13650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01207 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1)
theorem ha13650 : a13650.IsHomogeneous 39 := by
  unfold a13650
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a13651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02710 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01207 ^ 1)
theorem ha13651 : a13651.IsHomogeneous 39 := by
  unfold a13651
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02710.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a13652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13649 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a13650 ^ 1)
theorem ha13652 : a13652.IsHomogeneous 45 := by
  unfold a13652
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13651.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13649.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha13650.pow 1)))

@[irreducible]
def a13653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha13653 : a13653.IsHomogeneous 33 := by
  unfold a13653
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha13654 : a13654.IsHomogeneous 33 := by
  unfold a13654
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13653 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13649 ^ 1)
theorem ha13655 : a13655.IsHomogeneous 39 := by
  unfold a13655
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13653.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13654.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13649.pow 1)))

@[irreducible]
def a13656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha13656 : a13656.IsHomogeneous 33 := by
  unfold a13656
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a13657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13656 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13650 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a13653 ^ 1)
theorem ha13657 : a13657.IsHomogeneous 39 := by
  unfold a13657
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13650.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha13653.pow 1)))

@[irreducible]
def a13658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13652 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a13657 ^ 1)
theorem ha13658 : a13658.IsHomogeneous 45 := by
  unfold a13658
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13652.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha13657.pow 1)))

@[irreducible]
def a13659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01207 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1)
theorem ha13659 : a13659.IsHomogeneous 42 := by
  unfold a13659
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a13660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01207 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1)
theorem ha13660 : a13660.IsHomogeneous 42 := by
  unfold a13660
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01207.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a13661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13660 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13659 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13650 ^ 1)
theorem ha13661 : a13661.IsHomogeneous 48 := by
  unfold a13661
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13660.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13659.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13650.pow 1)))

@[irreducible]
def a13662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a05389 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02710 ^ 1)
theorem ha13662 : a13662.IsHomogeneous 42 := by
  unfold a13662
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha05389.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a13663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13659 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a13662 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13651 ^ 1)
theorem ha13663 : a13663.IsHomogeneous 42 := by
  unfold a13663
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13659.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha13662.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13651.pow 1)))

@[irreducible]
def a13664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13661 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13663 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13652 ^ 1)
theorem ha13664 : a13664.IsHomogeneous 48 := by
  unfold a13664
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13661.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13663.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13652.pow 1)))

@[irreducible]
def a13665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00042 ^ 1)
theorem ha13665 : a13665.IsHomogeneous 36 := by
  unfold a13665
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a13666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13665 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13660 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13656 ^ 1)
theorem ha13666 : a13666.IsHomogeneous 42 := by
  unfold a13666
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13665.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13660.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13656.pow 1)))

@[irreducible]
def a13667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13666 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13661 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13657 ^ 1)
theorem ha13667 : a13667.IsHomogeneous 48 := by
  unfold a13667
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13661.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13657.pow 1)))

@[irreducible]
def a13668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13664 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13667 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13658 ^ 1)
theorem ha13668 : a13668.IsHomogeneous 48 := by
  unfold a13668
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13664.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13667.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13658.pow 1)))

@[irreducible]
def a13669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01207 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a02710 ^ 1)
theorem ha13669 : a13669.IsHomogeneous 39 := by
  unfold a13669
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a13670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00865 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00455 ^ 1 * a02008 ^ 1)
theorem ha13670 : a13670.IsHomogeneous 39 := by
  unfold a13670
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00865.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13670 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a13669 ^ 1)
theorem ha13671 : a13671.IsHomogeneous 45 := by
  unfold a13671
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13649.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13670.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha13669.pow 1)))

@[irreducible]
def a13672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02710 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00129 ^ 1 * a05389 ^ 1)
theorem ha13672 : a13672.IsHomogeneous 39 := by
  unfold a13672
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02710.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00129.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a13673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13651 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a13672 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13669 ^ 1)
theorem ha13673 : a13673.IsHomogeneous 39 := by
  unfold a13673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha13672.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13669.pow 1)))

@[irreducible]
def a13674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13671 ^ 1)
theorem ha13674 : a13674.IsHomogeneous 45 := by
  unfold a13674
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13652.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13671.pow 1)))

@[irreducible]
def a13675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1)
theorem ha13675 : a13675.IsHomogeneous 30 := by
  unfold a13675
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13670 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13675 ^ 1)
theorem ha13676 : a13676.IsHomogeneous 39 := by
  unfold a13676
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13670.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13675.pow 1)))

@[irreducible]
def a13677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13676 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13671 ^ 1)
theorem ha13677 : a13677.IsHomogeneous 45 := by
  unfold a13677
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13676.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13671.pow 1)))

@[irreducible]
def a13678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13658 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13674 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13677 ^ 1)
theorem ha13678 : a13678.IsHomogeneous 45 := by
  unfold a13678
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13658.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13674.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13677.pow 1)))

@[irreducible]
def a13679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05389 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a10237 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a05389 ^ 1)
theorem ha13679 : a13679.IsHomogeneous 42 := by
  unfold a13679
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha10237.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a13680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13662 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a13679 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13672 ^ 1)
theorem ha13680 : a13680.IsHomogeneous 42 := by
  unfold a13680
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha13679.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13672.pow 1)))

@[irreducible]
def a13681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13663 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a13680 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13673 ^ 1)
theorem ha13681 : a13681.IsHomogeneous 42 := by
  unfold a13681
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13663.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha13680.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13673.pow 1)))

@[irreducible]
def a13682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13664 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13681 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13674 ^ 1)
theorem ha13682 : a13682.IsHomogeneous 48 := by
  unfold a13682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13664.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13681.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13674.pow 1)))

@[irreducible]
def a13683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13682 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13678 ^ 1)
theorem ha13683 : a13683.IsHomogeneous 48 := by
  unfold a13683
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13682.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13678.pow 1)))

@[irreducible]
def a13684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00316 ^ 1 * a00809 ^ 1)
theorem ha13684 : a13684.IsHomogeneous 42 := by
  unfold a13684
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00809 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00809 ^ 1)
theorem ha13685 : a13685.IsHomogeneous 33 := by
  unfold a13685
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha13686 : a13686.IsHomogeneous 36 := by
  unfold a13686
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13686 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13684 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13685 ^ 1)
theorem ha13687 : a13687.IsHomogeneous 42 := by
  unfold a13687
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13686.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13684.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13685.pow 1)))

@[irreducible]
def a13688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00126 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1)
theorem ha13688 : a13688.IsHomogeneous 42 := by
  unfold a13688
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a13689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00126 ^ 1 * a02007 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00864 ^ 1)
theorem ha13689 : a13689.IsHomogeneous 42 := by
  unfold a13689
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00126.pow 1)).mul (ha02007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a13690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13684 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13688 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a13689 ^ 1)
theorem ha13690 : a13690.IsHomogeneous 42 := by
  unfold a13690
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13684.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13688.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha13689.pow 1)))

@[irreducible]
def a13691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha13691 : a13691.IsHomogeneous 36 := by
  unfold a13691
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a13692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13686 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a13691 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13688 ^ 1)
theorem ha13692 : a13692.IsHomogeneous 42 := by
  unfold a13692
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13686.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha13691.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13688.pow 1)))

@[irreducible]
def a13693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13692 ^ 1)
theorem ha13693 : a13693.IsHomogeneous 42 := by
  unfold a13693
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13690.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13692.pow 1)))

@[irreducible]
def a13694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00809 ^ 1)
theorem ha13694 : a13694.IsHomogeneous 33 := by
  unfold a13694
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00809.pow 1)))

@[irreducible]
def a13695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03890 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01896 ^ 1)
theorem ha13695 : a13695.IsHomogeneous 33 := by
  unfold a13695
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01896.pow 1)))

@[irreducible]
def a13696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13694 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a13695 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13685 ^ 1)
theorem ha13696 : a13696.IsHomogeneous 39 := by
  unfold a13696
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13694.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha13695.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13685.pow 1)))

@[irreducible]
def a13697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00298 ^ 1)
theorem ha13697 : a13697.IsHomogeneous 36 := by
  unfold a13697
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00298.pow 1)))

@[irreducible]
def a13698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13697 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13694 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13686 ^ 1)
theorem ha13698 : a13698.IsHomogeneous 42 := by
  unfold a13698
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13697.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13694.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13686.pow 1)))

@[irreducible]
def a13699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13698 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13696 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13687 ^ 1)
theorem ha13699 : a13699.IsHomogeneous 48 := by
  unfold a13699
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13698.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13696.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13687.pow 1)))

@[irreducible]
def a13700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha13700 : a13700.IsHomogeneous 36 := by
  unfold a13700
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a13701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13697 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13700 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13691 ^ 1)
theorem ha13701 : a13701.IsHomogeneous 42 := by
  unfold a13701
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13697.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13700.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13691.pow 1)))

@[irreducible]
def a13702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13698 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13701 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13692 ^ 1)
theorem ha13702 : a13702.IsHomogeneous 48 := by
  unfold a13702
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13698.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13701.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13692.pow 1)))

@[irreducible]
def a13703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13699 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13702 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13693 ^ 1)
theorem ha13703 : a13703.IsHomogeneous 48 := by
  unfold a13703
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13699.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13702.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13693.pow 1)))

@[irreducible]
def a13704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a01896 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a00864 ^ 1)
theorem ha13704 : a13704.IsHomogeneous 39 := by
  unfold a13704
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a13705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a02007 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a00864 ^ 1)
theorem ha13705 : a13705.IsHomogeneous 42 := by
  unfold a13705
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a13706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13684 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13705 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13704 ^ 1)
theorem ha13706 : a13706.IsHomogeneous 42 := by
  unfold a13706
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13684.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13705.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13704.pow 1)))

@[irreducible]
def a13707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a03890 ^ 1)
theorem ha13707 : a13707.IsHomogeneous 33 := by
  unfold a13707
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13685 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13704 ^ 1)
theorem ha13708 : a13708.IsHomogeneous 39 := by
  unfold a13708
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13685.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13707.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13704.pow 1)))

@[irreducible]
def a13709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13706 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13708 ^ 1)
theorem ha13709 : a13709.IsHomogeneous 42 := by
  unfold a13709
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13706.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13708.pow 1)))

@[irreducible]
def a13710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a04085 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a02007 ^ 1)
theorem ha13710 : a13710.IsHomogeneous 42 := by
  unfold a13710
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha04085.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a13711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13689 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13710 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a13705 ^ 1)
theorem ha13711 : a13711.IsHomogeneous 42 := by
  unfold a13711
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13710.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha13705.pow 1)))

@[irreducible]
def a13712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13706 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a13711 ^ 1)
theorem ha13712 : a13712.IsHomogeneous 42 := by
  unfold a13712
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13690.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13706.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha13711.pow 1)))

@[irreducible]
def a13713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13693 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13712 ^ 1)
theorem ha13713 : a13713.IsHomogeneous 42 := by
  unfold a13713
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13693.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13709.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13712.pow 1)))

@[irreducible]
def a13714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03890 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07248 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a03890 ^ 1)
theorem ha13714 : a13714.IsHomogeneous 33 := by
  unfold a13714
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07248.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha03890.pow 1)))

@[irreducible]
def a13715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13695 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13714 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13707 ^ 1)
theorem ha13715 : a13715.IsHomogeneous 39 := by
  unfold a13715
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13695.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13714.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13707.pow 1)))

@[irreducible]
def a13716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13696 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a13715 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a13708 ^ 1)
theorem ha13716 : a13716.IsHomogeneous 45 := by
  unfold a13716
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13696.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha13715.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha13708.pow 1)))

@[irreducible]
def a13717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13699 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13716 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13709 ^ 1)
theorem ha13717 : a13717.IsHomogeneous 48 := by
  unfold a13717
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13699.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13716.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13709.pow 1)))

@[irreducible]
def a13718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13717 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13713 ^ 1)
theorem ha13718 : a13718.IsHomogeneous 48 := by
  unfold a13718
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13713.pow 1)))

@[irreducible]
def a13719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13683 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13718 ^ 1)
theorem ha13719 : a13719.IsHomogeneous 48 := by
  unfold a13719
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13718.pow 1)))

@[irreducible]
def a13720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13719 ^ 1)
theorem ha13720 : a13720.IsHomogeneous 48 := by
  unfold a13720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13719.pow 1)))

@[irreducible]
def a13721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13720 ^ 1)
theorem ha13721 : a13721.IsHomogeneous 48 := by
  unfold a13721
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13720.pow 1)))

@[irreducible]
def a13722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13718 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13719 ^ 1)
theorem ha13722 : a13722.IsHomogeneous 48 := by
  unfold a13722
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13719.pow 1)))

@[irreducible]
def a13723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13720 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13722 ^ 1)
theorem ha13723 : a13723.IsHomogeneous 48 := by
  unfold a13723
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13720.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13722.pow 1)))

@[irreducible]
def a13724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13723 ^ 1)
theorem ha13724 : a13724.IsHomogeneous 48 := by
  unfold a13724
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13723.pow 1)))

@[irreducible]
def a13725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13721 ^ 1)
theorem ha13725 : a13725.IsHomogeneous 48 := by
  unfold a13725
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13721.pow 1)))

@[irreducible]
def a13726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13725 ^ 1)
theorem ha13726 : a13726.IsHomogeneous 48 := by
  unfold a13726
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13725.pow 1)))

@[irreducible]
def a13727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13718 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13722 ^ 1)
theorem ha13727 : a13727.IsHomogeneous 48 := by
  unfold a13727
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13722.pow 1)))

@[irreducible]
def a13728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13723 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13727 ^ 1)
theorem ha13728 : a13728.IsHomogeneous 48 := by
  unfold a13728
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13727.pow 1)))

@[irreducible]
def a13729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13728 ^ 1)
theorem ha13729 : a13729.IsHomogeneous 48 := by
  unfold a13729
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13728.pow 1)))

@[irreducible]
def a13730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13726 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13729 ^ 1)
theorem ha13730 : a13730.IsHomogeneous 48 := by
  unfold a13730
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13729.pow 1)))

@[irreducible]
def a13731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11561 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a12186 ^ 1)
theorem ha13731 : a13731.IsHomogeneous 48 := by
  unfold a13731
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha12186.pow 1)))

@[irreducible]
def a13732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12186 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13731 ^ 1)
theorem ha13732 : a13732.IsHomogeneous 48 := by
  unfold a13732
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13731.pow 1)))

@[irreducible]
def a13733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13731 ^ 1)
theorem ha13733 : a13733.IsHomogeneous 48 := by
  unfold a13733
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13731.pow 1)))

@[irreducible]
def a13734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13732 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13733 ^ 1)
theorem ha13734 : a13734.IsHomogeneous 48 := by
  unfold a13734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13733.pow 1)))

@[irreducible]
def a13735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13733 ^ 1)
theorem ha13735 : a13735.IsHomogeneous 48 := by
  unfold a13735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13733.pow 1)))

@[irreducible]
def a13736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13734 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13735 ^ 1)
theorem ha13736 : a13736.IsHomogeneous 48 := by
  unfold a13736
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13734.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13735.pow 1)))

@[irreducible]
def a13737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13732 ^ 1)
theorem ha13737 : a13737.IsHomogeneous 48 := by
  unfold a13737
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13732.pow 1)))

@[irreducible]
def a13738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13734 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13737 ^ 1)
theorem ha13738 : a13738.IsHomogeneous 48 := by
  unfold a13738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13734.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13737.pow 1)))

@[irreducible]
def a13739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13738 ^ 1)
theorem ha13739 : a13739.IsHomogeneous 48 := by
  unfold a13739
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13738.pow 1)))

@[irreducible]
def a13740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13735 ^ 1)
theorem ha13740 : a13740.IsHomogeneous 48 := by
  unfold a13740
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13735.pow 1)))

@[irreducible]
def a13741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13736 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13740 ^ 1)
theorem ha13741 : a13741.IsHomogeneous 48 := by
  unfold a13741
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13740.pow 1)))

@[irreducible]
def a13742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13741 ^ 1)
theorem ha13742 : a13742.IsHomogeneous 48 := by
  unfold a13742
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13741.pow 1)))

@[irreducible]
def a13743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11660 ^ 1)
theorem ha13743 : a13743.IsHomogeneous 48 := by
  unfold a13743
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)))

@[irreducible]
def a13744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13743 ^ 1)
theorem ha13744 : a13744.IsHomogeneous 48 := by
  unfold a13744
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13743.pow 1)))

@[irreducible]
def a13745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13743 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11660 ^ 1)
theorem ha13745 : a13745.IsHomogeneous 48 := by
  unfold a13745
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13743.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)))

@[irreducible]
def a13746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13744 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13745 ^ 1)
theorem ha13746 : a13746.IsHomogeneous 48 := by
  unfold a13746
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13744.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13745.pow 1)))

@[irreducible]
def a13747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13744 ^ 1)
theorem ha13747 : a13747.IsHomogeneous 48 := by
  unfold a13747
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13744.pow 1)))

@[irreducible]
def a13748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13747 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a13746 ^ 1)
theorem ha13748 : a13748.IsHomogeneous 48 := by
  unfold a13748
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13747.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha13746.pow 1)))

@[irreducible]
def a13749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11660 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13743 ^ 1)
theorem ha13749 : a13749.IsHomogeneous 48 := by
  unfold a13749
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13743.pow 1)))

@[irreducible]
def a13750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13744 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a13749 ^ 1)
theorem ha13750 : a13750.IsHomogeneous 48 := by
  unfold a13750
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha13749.pow 1)))

@[irreducible]
def a13751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11660 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13749 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13745 ^ 1)
theorem ha13751 : a13751.IsHomogeneous 48 := by
  unfold a13751
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13749.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13745.pow 1)))

@[irreducible]
def a13752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13746 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13750 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a13751 ^ 1)
theorem ha13752 : a13752.IsHomogeneous 48 := by
  unfold a13752
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13750.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha13751.pow 1)))

@[irreducible]
def a13753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13747 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13750 ^ 1)
theorem ha13753 : a13753.IsHomogeneous 48 := by
  unfold a13753
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13750.pow 1)))

@[irreducible]
def a13754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13748 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13753 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a13752 ^ 1)
theorem ha13754 : a13754.IsHomogeneous 48 := by
  unfold a13754
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13753.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha13752.pow 1)))

@[irreducible]
def a13755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13749 ^ 1)
theorem ha13755 : a13755.IsHomogeneous 48 := by
  unfold a13755
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13749.pow 1)))

@[irreducible]
def a13756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13750 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a13755 ^ 1)
theorem ha13756 : a13756.IsHomogeneous 48 := by
  unfold a13756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13750.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha13755.pow 1)))

@[irreducible]
def a13757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11660 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13755 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a13751 ^ 1)
theorem ha13757 : a13757.IsHomogeneous 48 := by
  unfold a13757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13755.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha13751.pow 1)))

@[irreducible]
def a13758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13752 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13756 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a13757 ^ 1)
theorem ha13758 : a13758.IsHomogeneous 48 := by
  unfold a13758
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13752.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13756.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha13757.pow 1)))

@[irreducible]
def a13759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13753 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13756 ^ 1)
theorem ha13759 : a13759.IsHomogeneous 48 := by
  unfold a13759
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13756.pow 1)))

@[irreducible]
def a13760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13754 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13759 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a13758 ^ 1)
theorem ha13760 : a13760.IsHomogeneous 48 := by
  unfold a13760
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13754.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13759.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha13758.pow 1)))

@[irreducible]
def a13761 : Poly := (C ((-245 : ℂ) / (18 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11747 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a13760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13730 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13742 ^ 1)
theorem ha13761 : a13761.IsHomogeneous 48 := by
  unfold a13761
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-245 : ℂ) / (18 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha13760.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13730.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13742.pow 1)))

@[irreducible]
def a13762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00880 ^ 1 * a01678 ^ 1)
theorem ha13762 : a13762.IsHomogeneous 239 := by
  unfold a13762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha02041.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00880.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a13763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00327 ^ 1 * a03534 ^ 1)
theorem ha13763 : a13763.IsHomogeneous 197 := by
  unfold a13763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha01678.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a13764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13762 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13763 ^ 1)
theorem ha13764 : a13764.IsHomogeneous 239 := by
  unfold a13764
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13763.pow 1)))

@[irreducible]
def a13765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a04148 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a02041 ^ 1)
theorem ha13765 : a13765.IsHomogeneous 277 := by
  unfold a13765
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha04148.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a13766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13765 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a13762 ^ 1)
theorem ha13766 : a13766.IsHomogeneous 277 := by
  unfold a13766
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13765.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha13762.pow 1)))

@[irreducible]
def a13767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13766 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a13764 ^ 1)
theorem ha13767 : a13767.IsHomogeneous 277 := by
  unfold a13767
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13766.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha13764.pow 1)))

@[irreducible]
def a13768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a03534 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00134 ^ 1 * a06692 ^ 1)
theorem ha13768 : a13768.IsHomogeneous 152 := by
  unfold a13768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha03534.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha06692.pow 1)))

@[irreducible]
def a13769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13763 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13768 ^ 1)
theorem ha13769 : a13769.IsHomogeneous 197 := by
  unfold a13769
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13763.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13768.pow 1)))

@[irreducible]
def a13770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13764 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13769 ^ 1)
theorem ha13770 : a13770.IsHomogeneous 239 := by
  unfold a13770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13764.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13769.pow 1)))

@[irreducible]
def a13771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13767 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a13770 ^ 1)
theorem ha13771 : a13771.IsHomogeneous 277 := by
  unfold a13771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13767.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha13770.pow 1)))

@[irreducible]
def a13772 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a07663 ^ 1)
theorem ha13772 : a13772.IsHomogeneous 313 := by
  unfold a13772
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha07663.pow 1)))

@[irreducible]
def a13773 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a13765 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13772 ^ 1)
theorem ha13773 : a13773.IsHomogeneous 313 := by
  unfold a13773
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha13765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13772.pow 1)))

@[irreducible]
def a13774 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a13766 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13773 ^ 1)
theorem ha13774 : a13774.IsHomogeneous 313 := by
  unfold a13774
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha13766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13773.pow 1)))

@[irreducible]
def a13775 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a13767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13774 ^ 1)
theorem ha13775 : a13775.IsHomogeneous 313 := by
  unfold a13775
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha13767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13774.pow 1)))

@[irreducible]
def a13776 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a13771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13775 ^ 1)
theorem ha13776 : a13776.IsHomogeneous 313 := by
  unfold a13776
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha13771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13775.pow 1)))

@[irreducible]
def a13777 : Poly := (C ((-1 : ℂ) / (5248800 : ℂ)) * a00001 ^ 5 * a00003 ^ 6 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 6 * a00100 ^ 6 * a13761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13776 ^ 1)
theorem ha13777 : a13777.IsHomogeneous 313 := by
  unfold a13777
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5248800 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 6)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 6)).mul (ha00100.pow 6)).mul (ha13761.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13776.pow 1)))

@[irreducible]
def a13778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07775 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a13777 ^ 1)
theorem ha13778 : a13778.IsHomogeneous 313 := by
  unfold a13778
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha13777.pow 1)))

@[irreducible]
def a13779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13778 ^ 1)
theorem ha13779 : a13779.IsHomogeneous 313 := by
  unfold a13779
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13778.pow 1)))

@[irreducible]
def a13780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13643 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13779 ^ 1)
theorem ha13780 : a13780.IsHomogeneous 313 := by
  unfold a13780
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13643.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13779.pow 1)))

@[irreducible]
def a13781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13644 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13780 ^ 1)
theorem ha13781 : a13781.IsHomogeneous 313 := by
  unfold a13781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13780.pow 1)))

@[irreducible]
def a13782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13648 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13781 ^ 1)
theorem ha13782 : a13782.IsHomogeneous 313 := by
  unfold a13782
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13648.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13781.pow 1)))

@[irreducible]
def a13783 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a13782 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a07779 ^ 1)
theorem ha13783 : a13783.IsHomogeneous 871 := by
  unfold a13783
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha13782.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha07779.pow 1)))

@[irreducible]
def a13784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13636 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a13783 ^ 1)
theorem ha13784 : a13784.IsHomogeneous 1318 := by
  unfold a13784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13636.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha13783.pow 1)))

@[irreducible]
def a13785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13637 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13784 ^ 1)
theorem ha13785 : a13785.IsHomogeneous 1735 := by
  unfold a13785
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13637.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13784.pow 1)))

@[irreducible]
def a13786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13638 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13785 ^ 1)
theorem ha13786 : a13786.IsHomogeneous 2152 := by
  unfold a13786
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13638.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13785.pow 1)))

@[irreducible]
def a13787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07672 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a04155 ^ 1)
theorem ha13787 : a13787.IsHomogeneous 2569 := by
  unfold a13787
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07672.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha04155.pow 1)))

@[irreducible]
def a13788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13787 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13633 ^ 1)
theorem ha13788 : a13788.IsHomogeneous 2569 := by
  unfold a13788
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13787.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13633.pow 1)))

@[irreducible]
def a13789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13788 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13635 ^ 1)
theorem ha13789 : a13789.IsHomogeneous 2569 := by
  unfold a13789
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13788.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13635.pow 1)))

@[irreducible]
def a13790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13789 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13638 ^ 1)
theorem ha13790 : a13790.IsHomogeneous 2569 := by
  unfold a13790
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13789.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13638.pow 1)))

@[irreducible]
def a13791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13790 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13786 ^ 1)
theorem ha13791 : a13791.IsHomogeneous 2569 := by
  unfold a13791
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13790.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13786.pow 1)))

@[irreducible]
def a13792 : Poly := (C ((-9 : ℂ) / (20 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a13632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13791 ^ 1)
theorem ha13792 : a13792.IsHomogeneous 2986 := by
  unfold a13792
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (20 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha13632.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13791.pow 1)))

@[irreducible]
def a13793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a13792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 7 * a10696 ^ 1)
theorem ha13793 : a13793.IsHomogeneous 3014 := by
  unfold a13793
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha13792.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 7)).mul (ha10696.pow 1)))

@[irreducible]
def a13794 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07788 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13793 ^ 1)
theorem ha13794 : a13794.IsHomogeneous 3014 := by
  unfold a13794
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07788.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13793.pow 1)))

@[irreducible]
def a13795 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13794 ^ 1)
theorem ha13795 : a13795.IsHomogeneous 3014 := by
  unfold a13795
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13794.pow 1)))

@[irreducible]
def a13796 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10107 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13795 ^ 1)
theorem ha13796 : a13796.IsHomogeneous 3014 := by
  unfold a13796
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10107.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13795.pow 1)))

@[irreducible]
def a13797 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13796 ^ 1)
theorem ha13797 : a13797.IsHomogeneous 3014 := by
  unfold a13797
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13796.pow 1)))

@[irreducible]
def a13798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00934 ^ 1 * a04151 ^ 1) + (C ((25 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00364 ^ 1 * a07667 ^ 1)
theorem ha13798 : a13798.IsHomogeneous 1586 := by
  unfold a13798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00934.pow 1)).mul (ha04151.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha07667.pow 1)))

@[irreducible]
def a13799 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10108 ^ 1)
theorem ha13799 : a13799.IsHomogeneous 1943 := by
  unfold a13799
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13798.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10108.pow 1)))

@[irreducible]
def a13800 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10109 ^ 1)
theorem ha13800 : a13800.IsHomogeneous 2300 := by
  unfold a13800
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10109.pow 1)))

@[irreducible]
def a13801 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13800 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10110 ^ 1)
theorem ha13801 : a13801.IsHomogeneous 2657 := by
  unfold a13801
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13800.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10110.pow 1)))

@[irreducible]
def a13802 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13797 ^ 1)
theorem ha13802 : a13802.IsHomogeneous 3014 := by
  unfold a13802
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13801.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13797.pow 1)))

@[irreducible]
def a13803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02104 ^ 1 * a02112 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00935 ^ 1 * a04232 ^ 1)
theorem ha13803 : a13803.IsHomogeneous 1824 := by
  unfold a13803
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02104.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00935.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a13804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a04244 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02104 ^ 1 * a02112 ^ 1)
theorem ha13804 : a13804.IsHomogeneous 2241 := by
  unfold a13804
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha04244.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02104.pow 1)).mul (ha02112.pow 1)))

@[irreducible]
def a13805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13804 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13803 ^ 1)
theorem ha13805 : a13805.IsHomogeneous 2241 := by
  unfold a13805
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13804.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13803.pow 1)))

@[irreducible]
def a13806 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a07779 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a04232 ^ 1)
theorem ha13806 : a13806.IsHomogeneous 1407 := by
  unfold a13806
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha07779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a13807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13803 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13806 ^ 1)
theorem ha13807 : a13807.IsHomogeneous 1824 := by
  unfold a13807
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13803.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13806.pow 1)))

@[irreducible]
def a13808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13805 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13807 ^ 1)
theorem ha13808 : a13808.IsHomogeneous 2241 := by
  unfold a13808
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13805.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13807.pow 1)))

@[irreducible]
def a13809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07795 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a04244 ^ 1)
theorem ha13809 : a13809.IsHomogeneous 2658 := by
  unfold a13809
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07795.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha04244.pow 1)))

@[irreducible]
def a13810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13809 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13804 ^ 1)
theorem ha13810 : a13810.IsHomogeneous 2658 := by
  unfold a13810
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13809.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13804.pow 1)))

@[irreducible]
def a13811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13810 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13805 ^ 1)
theorem ha13811 : a13811.IsHomogeneous 2658 := by
  unfold a13811
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13810.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13805.pow 1)))

@[irreducible]
def a13812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13811 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13808 ^ 1)
theorem ha13812 : a13812.IsHomogeneous 2658 := by
  unfold a13812
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13811.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13808.pow 1)))

@[irreducible]
def a13813 : Poly := (C ((-54 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a13802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13812 ^ 1)
theorem ha13813 : a13813.IsHomogeneous 3075 := by
  unfold a13813
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-54 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha13802.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13812.pow 1)))

@[irreducible]
def a13814 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a13813 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a10104 ^ 1)
theorem ha13814 : a13814.IsHomogeneous 3082 := by
  unfold a13814
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha13813.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha10104.pow 1)))

@[irreducible]
def a13815 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07803 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13814 ^ 1)
theorem ha13815 : a13815.IsHomogeneous 3082 := by
  unfold a13815
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07803.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13814.pow 1)))

@[irreducible]
def a13816 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13815 ^ 1)
theorem ha13816 : a13816.IsHomogeneous 3082 := by
  unfold a13816
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13815.pow 1)))

@[irreducible]
def a13817 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09365 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13816 ^ 1)
theorem ha13817 : a13817.IsHomogeneous 3082 := by
  unfold a13817
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09365.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13816.pow 1)))

@[irreducible]
def a13818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02043 ^ 1 * a02115 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00937 ^ 1 * a04151 ^ 1)
theorem ha13818 : a13818.IsHomogeneous 2011 := by
  unfold a13818
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02043.pow 1)).mul (ha02115.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00937.pow 1)).mul (ha04151.pow 1)))

@[irreducible]
def a13819 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13818 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09364 ^ 1)
theorem ha13819 : a13819.IsHomogeneous 2368 := by
  unfold a13819
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13818.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09364.pow 1)))

@[irreducible]
def a13820 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09365 ^ 1)
theorem ha13820 : a13820.IsHomogeneous 2725 := by
  unfold a13820
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13819.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09365.pow 1)))

@[irreducible]
def a13821 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13817 ^ 1)
theorem ha13821 : a13821.IsHomogeneous 3082 := by
  unfold a13821
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13817.pow 1)))

@[irreducible]
def a13822 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00937 ^ 1 * a04232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02104 ^ 1 * a02116 ^ 1)
theorem ha13822 : a13822.IsHomogeneous 1892 := by
  unfold a13822
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00937.pow 1)).mul (ha04232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02104.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a13823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a04252 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02104 ^ 1 * a02116 ^ 1)
theorem ha13823 : a13823.IsHomogeneous 2309 := by
  unfold a13823
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha04252.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02104.pow 1)).mul (ha02116.pow 1)))

end CycleQ2Concrete
