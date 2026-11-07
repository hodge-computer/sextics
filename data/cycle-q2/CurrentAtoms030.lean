import Proposal.CurrentAtoms029

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a09472 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09471 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a04894 ^ 1)
theorem ha09472 : a09472.IsHomogeneous 132 := by
  unfold a09472
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09471.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09473 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a09472 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09462 ^ 1)
theorem ha09473 : a09473.IsHomogeneous 138 := by
  unfold a09473
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha09472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09462.pow 1)))

@[irreducible]
def a09474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09473 ^ 1)
theorem ha09474 : a09474.IsHomogeneous 138 := by
  unfold a09474
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09473.pow 1)))

@[irreducible]
def a09475 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a01041 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a03933 ^ 1)
theorem ha09475 : a09475.IsHomogeneous 135 := by
  unfold a09475
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha01041.pow 1)).mul (ha01923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha03933.pow 1)))

@[irreducible]
def a09476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09461 ^ 1) + (C ((27 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a09475 ^ 1)
theorem ha09476 : a09476.IsHomogeneous 138 := by
  unfold a09476
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha09475.pow 1)))

@[irreducible]
def a09477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09476 ^ 1)
theorem ha09477 : a09477.IsHomogeneous 138 := by
  unfold a09477
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09476.pow 1)))

@[irreducible]
def a09478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09477 ^ 1)
theorem ha09478 : a09478.IsHomogeneous 138 := by
  unfold a09478
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09474.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09477.pow 1)))

@[irreducible]
def a09479 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a01207 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a02710 ^ 1)
theorem ha09479 : a09479.IsHomogeneous 157 := by
  unfold a09479
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha01207.pow 1)).mul (ha01264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a09480 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a01207 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02814 ^ 1)
theorem ha09480 : a09480.IsHomogeneous 161 := by
  unfold a09480
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha01207.pow 1)).mul (ha01264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a09481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09480 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a09479 ^ 1)
theorem ha09481 : a09481.IsHomogeneous 161 := by
  unfold a09481
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09480.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha09479.pow 1)))

@[irreducible]
def a09482 : Poly := (C ((-7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00148 ^ 1 * a05389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a02710 ^ 1)
theorem ha09482 : a09482.IsHomogeneous 157 := by
  unfold a09482
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a09483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09482 ^ 1)
theorem ha09483 : a09483.IsHomogeneous 157 := by
  unfold a09483
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09482.pow 1)))

@[irreducible]
def a09484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09481 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a09483 ^ 1)
theorem ha09484 : a09484.IsHomogeneous 161 := by
  unfold a09484
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09481.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha09483.pow 1)))

@[irreducible]
def a09485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a05555 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00455 ^ 1 * a02814 ^ 1)
theorem ha09485 : a09485.IsHomogeneous 161 := by
  unfold a09485
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha05555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00455.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a09486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09480 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a09485 ^ 1)
theorem ha09486 : a09486.IsHomogeneous 161 := by
  unfold a09486
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha09485.pow 1)))

@[irreducible]
def a09487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09486 ^ 1)
theorem ha09487 : a09487.IsHomogeneous 161 := by
  unfold a09487
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09486.pow 1)))

@[irreducible]
def a09488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09487 ^ 1)
theorem ha09488 : a09488.IsHomogeneous 161 := by
  unfold a09488
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09487.pow 1)))

@[irreducible]
def a09489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09488 ^ 1) + (C ((8 : ℂ) / (2025 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00006 ^ 1 * a00014 ^ 2 * a09478 ^ 1)
theorem ha09489 : a09489.IsHomogeneous 161 := by
  unfold a09489
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09488.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (2025 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha09478.pow 1)))

@[irreducible]
def a09490 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a01083 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a02499 ^ 1)
theorem ha09490 : a09490.IsHomogeneous 183 := by
  unfold a09490
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha01083.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha02499.pow 1)))

@[irreducible]
def a09491 : Poly := (C ((-10 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00809 ^ 1 * a02499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a05047 ^ 1)
theorem ha09491 : a09491.IsHomogeneous 190 := by
  unfold a09491
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha02499.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha05047.pow 1)))

@[irreducible]
def a09492 : Poly := (C ((-10 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09490 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09491 ^ 1)
theorem ha09492 : a09492.IsHomogeneous 190 := by
  unfold a09492
  exact (((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09490.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09491.pow 1)))

@[irreducible]
def a09493 : Poly := (C ((-7 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00389 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01083 ^ 1 * a01896 ^ 1)
theorem ha09493 : a09493.IsHomogeneous 177 := by
  unfold a09493
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00389.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01083.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a09494 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a09493 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09490 ^ 1)
theorem ha09494 : a09494.IsHomogeneous 183 := by
  unfold a09494
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha09493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09490.pow 1)))

@[irreducible]
def a09495 : Poly := (C ((-10 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09494 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09492 ^ 1)
theorem ha09495 : a09495.IsHomogeneous 190 := by
  unfold a09495
  exact (((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09494.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09492.pow 1)))

@[irreducible]
def a09496 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01048 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a02432 ^ 1)
theorem ha09496 : a09496.IsHomogeneous 123 := by
  unfold a09496
  exact (((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01048.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha02432.pow 1)))

@[irreducible]
def a09497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a04933 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00829 ^ 1 * a02432 ^ 1)
theorem ha09497 : a09497.IsHomogeneous 123 := by
  unfold a09497
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04933.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00829.pow 1)).mul (ha02432.pow 1)))

@[irreducible]
def a09498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09496 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a09497 ^ 1)
theorem ha09498 : a09498.IsHomogeneous 123 := by
  unfold a09498
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha09497.pow 1)))

@[irreducible]
def a09499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02425 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01045 ^ 1)
theorem ha09499 : a09499.IsHomogeneous 33 := by
  unfold a09499
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02425.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01045.pow 1)))

@[irreducible]
def a09500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01045 ^ 1)
theorem ha09500 : a09500.IsHomogeneous 30 := by
  unfold a09500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01045.pow 1)))

@[irreducible]
def a09501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09500 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09499 ^ 1)
theorem ha09501 : a09501.IsHomogeneous 36 := by
  unfold a09501
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09500.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09499.pow 1)))

@[irreducible]
def a09502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02425 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a04919 ^ 1)
theorem ha09502 : a09502.IsHomogeneous 39 := by
  unfold a09502
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha04919.pow 1)))

@[irreducible]
def a09503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09502 ^ 1)
theorem ha09503 : a09503.IsHomogeneous 39 := by
  unfold a09503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09502.pow 1)))

@[irreducible]
def a09504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09501 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09503 ^ 1)
theorem ha09504 : a09504.IsHomogeneous 42 := by
  unfold a09504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09501.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09503.pow 1)))

@[irreducible]
def a09505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00864 ^ 1)
theorem ha09505 : a09505.IsHomogeneous 33 := by
  unfold a09505
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00865 ^ 1)
theorem ha09506 : a09506.IsHomogeneous 27 := by
  unfold a09506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a09507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09505 ^ 1)
theorem ha09507 : a09507.IsHomogeneous 33 := by
  unfold a09507
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09505.pow 1)))

@[irreducible]
def a09508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00864 ^ 1)
theorem ha09508 : a09508.IsHomogeneous 36 := by
  unfold a09508
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09508 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09505 ^ 1)
theorem ha09509 : a09509.IsHomogeneous 36 := by
  unfold a09509
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09508.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09505.pow 1)))

@[irreducible]
def a09510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09509 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09507 ^ 1)
theorem ha09510 : a09510.IsHomogeneous 36 := by
  unfold a09510
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09509.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09507.pow 1)))

@[irreducible]
def a09511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00865 ^ 1)
theorem ha09511 : a09511.IsHomogeneous 24 := by
  unfold a09511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00865.pow 1)))

@[irreducible]
def a09512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09511 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09506 ^ 1)
theorem ha09512 : a09512.IsHomogeneous 30 := by
  unfold a09512
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09506.pow 1)))

@[irreducible]
def a09513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09512 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09507 ^ 1)
theorem ha09513 : a09513.IsHomogeneous 36 := by
  unfold a09513
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09512.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09507.pow 1)))

@[irreducible]
def a09514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09513 ^ 1)
theorem ha09514 : a09514.IsHomogeneous 36 := by
  unfold a09514
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09513.pow 1)))

@[irreducible]
def a09515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a09514 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04919 ^ 1)
theorem ha09515 : a09515.IsHomogeneous 42 := by
  unfold a09515
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha09514.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04919.pow 1)))

@[irreducible]
def a09516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09515 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09502 ^ 1)
theorem ha09516 : a09516.IsHomogeneous 42 := by
  unfold a09516
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09515.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09502.pow 1)))

@[irreducible]
def a09517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09516 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09503 ^ 1)
theorem ha09517 : a09517.IsHomogeneous 42 := by
  unfold a09517
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09516.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09503.pow 1)))

@[irreducible]
def a09518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09504 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a09517 ^ 1)
theorem ha09518 : a09518.IsHomogeneous 42 := by
  unfold a09518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha09517.pow 1)))

@[irreducible]
def a09519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1)
theorem ha09519 : a09519.IsHomogeneous 18 := by
  unfold a09519
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a09520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1)
theorem ha09520 : a09520.IsHomogeneous 12 := by
  unfold a09520
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a09521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00324 ^ 1)
theorem ha09521 : a09521.IsHomogeneous 12 := by
  unfold a09521
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a09522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09519 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09520 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09521 ^ 1)
theorem ha09522 : a09522.IsHomogeneous 18 := by
  unfold a09522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09519.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09521.pow 1)))

@[irreducible]
def a09523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1)
theorem ha09523 : a09523.IsHomogeneous 12 := by
  unfold a09523
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a09524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1)
theorem ha09524 : a09524.IsHomogeneous 24 := by
  unfold a09524
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a09525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09524 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a09523 ^ 1)
theorem ha09525 : a09525.IsHomogeneous 24 := by
  unfold a09525
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09524.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha09523.pow 1)))

@[irreducible]
def a09526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha09526 : a09526.IsHomogeneous 12 := by
  unfold a09526
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a09527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09520 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09526 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09523 ^ 1)
theorem ha09527 : a09527.IsHomogeneous 18 := by
  unfold a09527
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09526.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09523.pow 1)))

@[irreducible]
def a09528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09525 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09527 ^ 1)
theorem ha09528 : a09528.IsHomogeneous 24 := by
  unfold a09528
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09525.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09527.pow 1)))

@[irreducible]
def a09529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1)
theorem ha09529 : a09529.IsHomogeneous 18 := by
  unfold a09529
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a09530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00864 ^ 1)
theorem ha09530 : a09530.IsHomogeneous 24 := by
  unfold a09530
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09519 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a09529 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a09530 ^ 1)
theorem ha09531 : a09531.IsHomogeneous 24 := by
  unfold a09531
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09519.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha09529.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha09530.pow 1)))

@[irreducible]
def a09532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09529 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00525 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09521 ^ 1)
theorem ha09532 : a09532.IsHomogeneous 18 := by
  unfold a09532
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09529.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00525.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09521.pow 1)))

@[irreducible]
def a09533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09531 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a09532 ^ 1)
theorem ha09533 : a09533.IsHomogeneous 24 := by
  unfold a09533
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09531.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha09532.pow 1)))

@[irreducible]
def a09534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00864 ^ 1)
theorem ha09534 : a09534.IsHomogeneous 24 := by
  unfold a09534
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09524 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a09534 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a09530 ^ 1)
theorem ha09535 : a09535.IsHomogeneous 24 := by
  unfold a09535
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha09534.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha09530.pow 1)))

@[irreducible]
def a09536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09531 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09535 ^ 1)
theorem ha09536 : a09536.IsHomogeneous 24 := by
  unfold a09536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09525.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09531.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09535.pow 1)))

@[irreducible]
def a09537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09536 ^ 1)
theorem ha09537 : a09537.IsHomogeneous 24 := by
  unfold a09537
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09533.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09536.pow 1)))

@[irreducible]
def a09538 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a09537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09518 ^ 1)
theorem ha09538 : a09538.IsHomogeneous 42 := by
  unfold a09538
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha09537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09518.pow 1)))

@[irreducible]
def a09539 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a09538 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04933 ^ 1)
theorem ha09539 : a09539.IsHomogeneous 87 := by
  unfold a09539
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha09538.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04933.pow 1)))

@[irreducible]
def a09540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09539 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09497 ^ 1)
theorem ha09540 : a09540.IsHomogeneous 123 := by
  unfold a09540
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09497.pow 1)))

@[irreducible]
def a09541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09498 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a09540 ^ 1)
theorem ha09541 : a09541.IsHomogeneous 123 := by
  unfold a09541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha09540.pow 1)))

@[irreducible]
def a09542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a03963 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01048 ^ 1 * a01938 ^ 1)
theorem ha09542 : a09542.IsHomogeneous 123 := by
  unfold a09542
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha03963.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01048.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a09543 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a09542 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09496 ^ 1)
theorem ha09543 : a09543.IsHomogeneous 123 := by
  unfold a09543
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha09542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09496.pow 1)))

@[irreducible]
def a09544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09543 ^ 1)
theorem ha09544 : a09544.IsHomogeneous 123 := by
  unfold a09544
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09543.pow 1)))

@[irreducible]
def a09545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09544 ^ 1)
theorem ha09545 : a09545.IsHomogeneous 123 := by
  unfold a09545
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09544.pow 1)))

@[irreducible]
def a09546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01223 ^ 1 * a01275 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00484 ^ 1 * a02744 ^ 1)
theorem ha09546 : a09546.IsHomogeneous 142 := by
  unfold a09546
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01223.pow 1)).mul (ha01275.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00484.pow 1)).mul (ha02744.pow 1)))

@[irreducible]
def a09547 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00459 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01223 ^ 1 * a01275 ^ 1)
theorem ha09547 : a09547.IsHomogeneous 148 := by
  unfold a09547
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00459.pow 1)).mul (ha02837.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01223.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a09548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09546 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09547 ^ 1)
theorem ha09548 : a09548.IsHomogeneous 148 := by
  unfold a09548
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09547.pow 1)))

@[irreducible]
def a09549 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a05448 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02744 ^ 1)
theorem ha09549 : a09549.IsHomogeneous 136 := by
  unfold a09549
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha05448.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02744.pow 1)))

@[irreducible]
def a09550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09546 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a09549 ^ 1)
theorem ha09550 : a09550.IsHomogeneous 142 := by
  unfold a09550
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09546.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha09549.pow 1)))

@[irreducible]
def a09551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09548 ^ 1)
theorem ha09551 : a09551.IsHomogeneous 148 := by
  unfold a09551
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09548.pow 1)))

@[irreducible]
def a09552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00137 ^ 1 * a05595 ^ 1)
theorem ha09552 : a09552.IsHomogeneous 155 := by
  unfold a09552
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00137.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a09553 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09552 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09547 ^ 1)
theorem ha09553 : a09553.IsHomogeneous 155 := by
  unfold a09553
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09552.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09547.pow 1)))

@[irreducible]
def a09554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09553 ^ 1)
theorem ha09554 : a09554.IsHomogeneous 155 := by
  unfold a09554
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09553.pow 1)))

@[irreducible]
def a09555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09554 ^ 1)
theorem ha09555 : a09555.IsHomogeneous 155 := by
  unfold a09555
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09554.pow 1)))

@[irreducible]
def a09556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09555 ^ 1) + (C ((54 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a09545 ^ 1)
theorem ha09556 : a09556.IsHomogeneous 155 := by
  unfold a09556
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09555.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha09545.pow 1)))

@[irreducible]
def a09557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02496 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01081 ^ 1 * a01841 ^ 1)
theorem ha09557 : a09557.IsHomogeneous 144 := by
  unfold a09557
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02496.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01081.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a09558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02496 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a05043 ^ 1)
theorem ha09558 : a09558.IsHomogeneous 144 := by
  unfold a09558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02496.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha05043.pow 1)))

@[irreducible]
def a09559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09557 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09558 ^ 1)
theorem ha09559 : a09559.IsHomogeneous 144 := by
  unfold a09559
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09558.pow 1)))

@[irreducible]
def a09560 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a01081 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00388 ^ 1 * a03803 ^ 1)
theorem ha09560 : a09560.IsHomogeneous 144 := by
  unfold a09560
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha01081.pow 1)).mul (ha01841.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00388.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a09561 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a09560 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09557 ^ 1)
theorem ha09561 : a09561.IsHomogeneous 144 := by
  unfold a09561
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha09560.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09557.pow 1)))

@[irreducible]
def a09562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09561 ^ 1)
theorem ha09562 : a09562.IsHomogeneous 144 := by
  unfold a09562
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09561.pow 1)))

@[irreducible]
def a09563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01052 ^ 1 * a01917 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a02441 ^ 1)
theorem ha09563 : a09563.IsHomogeneous 125 := by
  unfold a09563
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01052.pow 1)).mul (ha01917.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a09564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00301 ^ 1 * a04950 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00819 ^ 1 * a02441 ^ 1)
theorem ha09564 : a09564.IsHomogeneous 119 := by
  unfold a09564
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha04950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00819.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a09565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09564 ^ 1) + (C ((81 : ℂ) / (5 : ℂ)) * a09563 ^ 1)
theorem ha09565 : a09565.IsHomogeneous 125 := by
  unfold a09565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09564.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (5 : ℂ))).mul (ha09563.pow 1)))

@[irreducible]
def a09566 : Poly := (C ((-14 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a03811 ^ 1)
theorem ha09566 : a09566.IsHomogeneous 13 := by
  unfold a09566
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a09567 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a09566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a04950 ^ 1)
theorem ha09567 : a09567.IsHomogeneous 109 := by
  unfold a09567
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha04950.pow 1)))

@[irreducible]
def a09568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a09567 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09564 ^ 1)
theorem ha09568 : a09568.IsHomogeneous 119 := by
  unfold a09568
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha09567.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09564.pow 1)))

@[irreducible]
def a09569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09568 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09565 ^ 1)
theorem ha09569 : a09569.IsHomogeneous 125 := by
  unfold a09569
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09565.pow 1)))

@[irreducible]
def a09570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a03925 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a01052 ^ 1 * a01917 ^ 1)
theorem ha09570 : a09570.IsHomogeneous 124 := by
  unfold a09570
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha03925.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha01052.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a09571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09570 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a09563 ^ 1)
theorem ha09571 : a09571.IsHomogeneous 125 := by
  unfold a09571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha09563.pow 1)))

@[irreducible]
def a09572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09565 ^ 1) + (C ((27 : ℂ) / (4 : ℂ)) * a09571 ^ 1)
theorem ha09572 : a09572.IsHomogeneous 125 := by
  unfold a09572
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (4 : ℂ))).mul (ha09571.pow 1)))

@[irreducible]
def a09573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09572 ^ 1)
theorem ha09573 : a09573.IsHomogeneous 125 := by
  unfold a09573
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09572.pow 1)))

@[irreducible]
def a09574 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a01228 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00476 ^ 1 * a02754 ^ 1)
theorem ha09574 : a09574.IsHomogeneous 124 := by
  unfold a09574
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha01228.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a09575 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00461 ^ 1 * a02806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01228 ^ 1 * a01258 ^ 1)
theorem ha09575 : a09575.IsHomogeneous 124 := by
  unfold a09575
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00461.pow 1)).mul (ha02806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01228.pow 1)).mul (ha01258.pow 1)))

@[irreducible]
def a09576 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a09575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09574 ^ 1)
theorem ha09576 : a09576.IsHomogeneous 124 := by
  unfold a09576
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha09575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09574.pow 1)))

@[irreducible]
def a09577 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00146 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a02754 ^ 1)
theorem ha09577 : a09577.IsHomogeneous 118 := by
  unfold a09577
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a09578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09577 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09574 ^ 1)
theorem ha09578 : a09578.IsHomogeneous 124 := by
  unfold a09578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09577.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09574.pow 1)))

@[irreducible]
def a09579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09578 ^ 1)
theorem ha09579 : a09579.IsHomogeneous 124 := by
  unfold a09579
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09578.pow 1)))

@[irreducible]
def a09580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a02806 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00138 ^ 1 * a05545 ^ 1)
theorem ha09580 : a09580.IsHomogeneous 125 := by
  unfold a09580
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha02806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00138.pow 1)).mul (ha05545.pow 1)))

@[irreducible]
def a09581 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09575 ^ 1)
theorem ha09581 : a09581.IsHomogeneous 125 := by
  unfold a09581
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09580.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09575.pow 1)))

@[irreducible]
def a09582 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a09581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09576 ^ 1)
theorem ha09582 : a09582.IsHomogeneous 125 := by
  unfold a09582
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha09581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09576.pow 1)))

@[irreducible]
def a09583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09582 ^ 1)
theorem ha09583 : a09583.IsHomogeneous 125 := by
  unfold a09583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09579.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09582.pow 1)))

@[irreducible]
def a09584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09573 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a09583 ^ 1)
theorem ha09584 : a09584.IsHomogeneous 125 := by
  unfold a09584
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha09583.pow 1)))

@[irreducible]
def a09585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a02493 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a01079 ^ 1 * a01903 ^ 1)
theorem ha09585 : a09585.IsHomogeneous 123 := by
  unfold a09585
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha02493.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha01079.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a09586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a02493 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00299 ^ 1 * a05039 ^ 1)
theorem ha09586 : a09586.IsHomogeneous 129 := by
  unfold a09586
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha02493.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00299.pow 1)).mul (ha05039.pow 1)))

@[irreducible]
def a09587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09585 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09586 ^ 1)
theorem ha09587 : a09587.IsHomogeneous 129 := by
  unfold a09587
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09585.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09586.pow 1)))

@[irreducible]
def a09588 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00387 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01079 ^ 1 * a01903 ^ 1)
theorem ha09588 : a09588.IsHomogeneous 117 := by
  unfold a09588
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01079.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a09589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09585 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09588 ^ 1)
theorem ha09589 : a09589.IsHomogeneous 123 := by
  unfold a09589
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09585.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09588.pow 1)))

@[irreducible]
def a09590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09587 ^ 1)
theorem ha09590 : a09590.IsHomogeneous 129 := by
  unfold a09590
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09587.pow 1)))

@[irreducible]
def a09591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a02461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01060 ^ 1 * a01702 ^ 1)
theorem ha09591 : a09591.IsHomogeneous 94 := by
  unfold a09591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha02461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01060.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a04988 ^ 1)
theorem ha09592 : a09592.IsHomogeneous 95 := by
  unfold a09592
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02461.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha04988.pow 1)))

@[irreducible]
def a09593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09592 ^ 1)
theorem ha09593 : a09593.IsHomogeneous 95 := by
  unfold a09593
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09591.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09592.pow 1)))

@[irreducible]
def a09594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01060 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00375 ^ 1 * a03562 ^ 1)
theorem ha09594 : a09594.IsHomogeneous 94 := by
  unfold a09594
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01060.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00375.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a09595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09594 ^ 1)
theorem ha09595 : a09595.IsHomogeneous 94 := by
  unfold a09595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09591.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09594.pow 1)))

@[irreducible]
def a09596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09593 ^ 1)
theorem ha09596 : a09596.IsHomogeneous 95 := by
  unfold a09596
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09595.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09593.pow 1)))

@[irreducible]
def a09597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00317 ^ 1 * a02413 ^ 1)
theorem ha09597 : a09597.IsHomogeneous 39 := by
  unfold a09597
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00317.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a04894 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02413 ^ 1)
theorem ha09598 : a09598.IsHomogeneous 39 := by
  unfold a09598
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha04894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09597 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a09598 ^ 1)
theorem ha09599 : a09599.IsHomogeneous 39 := by
  unfold a09599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha09598.pow 1)))

@[irreducible]
def a09600 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00368 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01041 ^ 1)
theorem ha09600 : a09600.IsHomogeneous 33 := by
  unfold a09600
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09597 ^ 1)
theorem ha09601 : a09601.IsHomogeneous 39 := by
  unfold a09601
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09597.pow 1)))

@[irreducible]
def a09602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09599 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09601 ^ 1)
theorem ha09602 : a09602.IsHomogeneous 39 := by
  unfold a09602
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09599.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09601.pow 1)))

@[irreducible]
def a09603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a04894 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a09471 ^ 1)
theorem ha09603 : a09603.IsHomogeneous 39 := by
  unfold a09603
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha04894.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha09471.pow 1)))

@[irreducible]
def a09604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09598 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09603 ^ 1)
theorem ha09604 : a09604.IsHomogeneous 39 := by
  unfold a09604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09598.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09603.pow 1)))

@[irreducible]
def a09605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09599 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a09604 ^ 1)
theorem ha09605 : a09605.IsHomogeneous 39 := by
  unfold a09605
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09599.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha09604.pow 1)))

@[irreducible]
def a09606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09605 ^ 1)
theorem ha09606 : a09606.IsHomogeneous 39 := by
  unfold a09606
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09605.pow 1)))

@[irreducible]
def a09607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a02710 ^ 1)
theorem ha09607 : a09607.IsHomogeneous 18 := by
  unfold a09607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01207.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha02710.pow 1)))

@[irreducible]
def a09608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00316 ^ 1 * a01207 ^ 1)
theorem ha09608 : a09608.IsHomogeneous 24 := by
  unfold a09608
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a09609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09608 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09607 ^ 1)
theorem ha09609 : a09609.IsHomogeneous 24 := by
  unfold a09609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09608.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09607.pow 1)))

@[irreducible]
def a09610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02007 ^ 1)
theorem ha09610 : a09610.IsHomogeneous 24 := by
  unfold a09610
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a09611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09608 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09610 ^ 1)
theorem ha09611 : a09611.IsHomogeneous 24 := by
  unfold a09611
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09608.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09610.pow 1)))

@[irreducible]
def a09612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09611 ^ 1)
theorem ha09612 : a09612.IsHomogeneous 24 := by
  unfold a09612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09611.pow 1)))

@[irreducible]
def a09613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05389 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a02710 ^ 1)
theorem ha09613 : a09613.IsHomogeneous 24 := by
  unfold a09613
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha02710.pow 1)))

@[irreducible]
def a09614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09613 ^ 1) + (C ((135 : ℂ) / (28 : ℂ)) * a00003 ^ 6 * a09607 ^ 1)
theorem ha09614 : a09614.IsHomogeneous 24 := by
  unfold a09614
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09613.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (28 : ℂ))).mul (ha00003.pow 6)).mul (ha09607.pow 1)))

@[irreducible]
def a09615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09609 ^ 1) + (C ((7 : ℂ) / (27 : ℂ)) * a09614 ^ 1)
theorem ha09615 : a09615.IsHomogeneous 24 := by
  unfold a09615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (27 : ℂ))).mul (ha09614.pow 1)))

@[irreducible]
def a09616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09615 ^ 1)
theorem ha09616 : a09616.IsHomogeneous 24 := by
  unfold a09616
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09612.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09615.pow 1)))

@[irreducible]
def a09617 : Poly := (C ((-8 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09616 ^ 1)
theorem ha09617 : a09617.IsHomogeneous 44 := by
  unfold a09617
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09606.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09616.pow 1)))

@[irreducible]
def a09618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00298 ^ 1 * a01327 ^ 1)
theorem ha09618 : a09618.IsHomogeneous 39 := by
  unfold a09618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00298.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a09619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a01327 ^ 1)
theorem ha09619 : a09619.IsHomogeneous 36 := by
  unfold a09619
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a09620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09618 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a09619 ^ 1)
theorem ha09620 : a09620.IsHomogeneous 39 := by
  unfold a09620
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09618.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha09619.pow 1)))

@[irreducible]
def a09621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01896 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00809 ^ 1)
theorem ha09621 : a09621.IsHomogeneous 39 := by
  unfold a09621
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a09622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09618 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a09621 ^ 1)
theorem ha09622 : a09622.IsHomogeneous 39 := by
  unfold a09622
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha09621.pow 1)))

@[irreducible]
def a09623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09622 ^ 1)
theorem ha09623 : a09623.IsHomogeneous 39 := by
  unfold a09623
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09622.pow 1)))

@[irreducible]
def a09624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03890 ^ 1)
theorem ha09624 : a09624.IsHomogeneous 33 := by
  unfold a09624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a09625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09624 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09621 ^ 1)
theorem ha09625 : a09625.IsHomogeneous 39 := by
  unfold a09625
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09624.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09621.pow 1)))

@[irreducible]
def a09626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09622 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a09625 ^ 1)
theorem ha09626 : a09626.IsHomogeneous 39 := by
  unfold a09626
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha09625.pow 1)))

@[irreducible]
def a09627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09626 ^ 1)
theorem ha09627 : a09627.IsHomogeneous 39 := by
  unfold a09627
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09626.pow 1)))

@[irreducible]
def a09628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09617 ^ 1) + (C ((16 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09627 ^ 1)
theorem ha09628 : a09628.IsHomogeneous 44 := by
  unfold a09628
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09617.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09627.pow 1)))

@[irreducible]
def a09629 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a04988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a09628 ^ 1)
theorem ha09629 : a09629.IsHomogeneous 89 := by
  unfold a09629
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha04988.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha09628.pow 1)))

@[irreducible]
def a09630 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09629 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09592 ^ 1)
theorem ha09630 : a09630.IsHomogeneous 95 := by
  unfold a09630
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09592.pow 1)))

@[irreducible]
def a09631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09593 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09630 ^ 1)
theorem ha09631 : a09631.IsHomogeneous 95 := by
  unfold a09631
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09593.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09630.pow 1)))

@[irreducible]
def a09632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09631 ^ 1)
theorem ha09632 : a09632.IsHomogeneous 95 := by
  unfold a09632
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09631.pow 1)))

@[irreducible]
def a09633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00465 ^ 1 * a01678 ^ 1)
theorem ha09633 : a09633.IsHomogeneous 95 := by
  unfold a09633
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha01240.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00465.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02778 ^ 1)
theorem ha09634 : a09634.IsHomogeneous 94 := by
  unfold a09634
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a09635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09633 ^ 1)
theorem ha09635 : a09635.IsHomogeneous 95 := by
  unfold a09635
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09633.pow 1)))

@[irreducible]
def a09636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00139 ^ 1 * a03534 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00465 ^ 1 * a01678 ^ 1)
theorem ha09636 : a09636.IsHomogeneous 89 := by
  unfold a09636
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00139.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00465.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09633 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09636 ^ 1)
theorem ha09637 : a09637.IsHomogeneous 95 := by
  unfold a09637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09633.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09636.pow 1)))

@[irreducible]
def a09638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09635 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09637 ^ 1)
theorem ha09638 : a09638.IsHomogeneous 95 := by
  unfold a09638
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09635.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09637.pow 1)))

@[irreducible]
def a09639 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a05504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02778 ^ 1)
theorem ha09639 : a09639.IsHomogeneous 94 := by
  unfold a09639
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha05504.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a09640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09639 ^ 1)
theorem ha09640 : a09640.IsHomogeneous 94 := by
  unfold a09640
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09639.pow 1)))

@[irreducible]
def a09641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09640 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09635 ^ 1)
theorem ha09641 : a09641.IsHomogeneous 95 := by
  unfold a09641
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09640.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09635.pow 1)))

@[irreducible]
def a09642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09638 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09641 ^ 1)
theorem ha09642 : a09642.IsHomogeneous 95 := by
  unfold a09642
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09641.pow 1)))

@[irreducible]
def a09643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09632 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a09642 ^ 1)
theorem ha09643 : a09643.IsHomogeneous 95 := by
  unfold a09643
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha09642.pow 1)))

@[irreducible]
def a09644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00637 ^ 1 * a00817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a01581 ^ 1)
theorem ha09644 : a09644.IsHomogeneous 112 := by
  unfold a09644
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00637.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00637 ^ 1 * a00817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00211 ^ 1 * a01914 ^ 1)
theorem ha09645 : a09645.IsHomogeneous 105 := by
  unfold a09645
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00637.pow 1)).mul (ha00817.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00211.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a09646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09645 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09644 ^ 1)
theorem ha09646 : a09646.IsHomogeneous 112 := by
  unfold a09646
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09644.pow 1)))

@[irreducible]
def a09647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00042 ^ 1 * a00126 ^ 1 * a03370 ^ 1) + (C ((81 : ℂ) / (4 : ℂ)) * a00300 ^ 1 * a01581 ^ 1)
theorem ha09647 : a09647.IsHomogeneous 112 := by
  unfold a09647
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha03370.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (4 : ℂ))).mul (ha00300.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09644 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a09647 ^ 1)
theorem ha09648 : a09648.IsHomogeneous 112 := by
  unfold a09648
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha09647.pow 1)))

@[irreducible]
def a09649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09646 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09648 ^ 1)
theorem ha09649 : a09649.IsHomogeneous 112 := by
  unfold a09649
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09648.pow 1)))

@[irreducible]
def a09650 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00061 ^ 1 * a03921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01914 ^ 1)
theorem ha09650 : a09650.IsHomogeneous 99 := by
  unfold a09650
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha03921.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a09651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09650 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09645 ^ 1)
theorem ha09651 : a09651.IsHomogeneous 105 := by
  unfold a09651
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09650.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09645.pow 1)))

@[irreducible]
def a09652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09646 ^ 1)
theorem ha09652 : a09652.IsHomogeneous 112 := by
  unfold a09652
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09646.pow 1)))

@[irreducible]
def a09653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09652 ^ 1)
theorem ha09653 : a09653.IsHomogeneous 112 := by
  unfold a09653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09652.pow 1)))

@[irreducible]
def a09654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09653 ^ 1) + (C ((9 : ℂ) / (320 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a09643 ^ 1)
theorem ha09654 : a09654.IsHomogeneous 112 := by
  unfold a09654
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09653.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (320 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09643.pow 1)))

@[irreducible]
def a09655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a02474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01067 ^ 1 * a01702 ^ 1)
theorem ha09655 : a09655.IsHomogeneous 94 := by
  unfold a09655
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha02474.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01067.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a05010 ^ 1)
theorem ha09656 : a09656.IsHomogeneous 95 := by
  unfold a09656
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02474.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha05010.pow 1)))

@[irreducible]
def a09657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09656 ^ 1)
theorem ha09657 : a09657.IsHomogeneous 95 := by
  unfold a09657
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09656.pow 1)))

@[irreducible]
def a09658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01067 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00379 ^ 1 * a03562 ^ 1)
theorem ha09658 : a09658.IsHomogeneous 94 := by
  unfold a09658
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01067.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00379.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a09659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09658 ^ 1)
theorem ha09659 : a09659.IsHomogeneous 94 := by
  unfold a09659
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09658.pow 1)))

@[irreducible]
def a09660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09659 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09657 ^ 1)
theorem ha09660 : a09660.IsHomogeneous 95 := by
  unfold a09660
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09659.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09657.pow 1)))

@[irreducible]
def a09661 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09616 ^ 1)
theorem ha09661 : a09661.IsHomogeneous 44 := by
  unfold a09661
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09606.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09616.pow 1)))

@[irreducible]
def a09662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09661 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09627 ^ 1)
theorem ha09662 : a09662.IsHomogeneous 44 := by
  unfold a09662
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09661.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09627.pow 1)))

@[irreducible]
def a09663 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a05010 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a09662 ^ 1)
theorem ha09663 : a09663.IsHomogeneous 89 := by
  unfold a09663
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha05010.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha09662.pow 1)))

@[irreducible]
def a09664 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09656 ^ 1)
theorem ha09664 : a09664.IsHomogeneous 95 := by
  unfold a09664
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09663.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09656.pow 1)))

@[irreducible]
def a09665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09657 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09664 ^ 1)
theorem ha09665 : a09665.IsHomogeneous 95 := by
  unfold a09665
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09657.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09664.pow 1)))

@[irreducible]
def a09666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09665 ^ 1)
theorem ha09666 : a09666.IsHomogeneous 95 := by
  unfold a09666
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09665.pow 1)))

@[irreducible]
def a09667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00469 ^ 1 * a01678 ^ 1)
theorem ha09667 : a09667.IsHomogeneous 95 := by
  unfold a09667
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha01248.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00469.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02792 ^ 1)
theorem ha09668 : a09668.IsHomogeneous 94 := by
  unfold a09668
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a09669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09667 ^ 1)
theorem ha09669 : a09669.IsHomogeneous 95 := by
  unfold a09669
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09667.pow 1)))

@[irreducible]
def a09670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00141 ^ 1 * a03534 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00469 ^ 1 * a01678 ^ 1)
theorem ha09670 : a09670.IsHomogeneous 89 := by
  unfold a09670
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00141.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00469.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09667 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09670 ^ 1)
theorem ha09671 : a09671.IsHomogeneous 95 := by
  unfold a09671
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09667.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09670.pow 1)))

@[irreducible]
def a09672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09671 ^ 1)
theorem ha09672 : a09672.IsHomogeneous 95 := by
  unfold a09672
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09671.pow 1)))

@[irreducible]
def a09673 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a05526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02792 ^ 1)
theorem ha09673 : a09673.IsHomogeneous 94 := by
  unfold a09673
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha05526.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a09674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09673 ^ 1)
theorem ha09674 : a09674.IsHomogeneous 94 := by
  unfold a09674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09673.pow 1)))

@[irreducible]
def a09675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09674 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09669 ^ 1)
theorem ha09675 : a09675.IsHomogeneous 95 := by
  unfold a09675
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09674.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09669.pow 1)))

@[irreducible]
def a09676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09675 ^ 1)
theorem ha09676 : a09676.IsHomogeneous 95 := by
  unfold a09676
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09675.pow 1)))

@[irreducible]
def a09677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09666 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a09676 ^ 1)
theorem ha09677 : a09677.IsHomogeneous 95 := by
  unfold a09677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha09676.pow 1)))

@[irreducible]
def a09678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09653 ^ 1) + (C ((1 : ℂ) / (40 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a09677 ^ 1)
theorem ha09678 : a09678.IsHomogeneous 112 := by
  unfold a09678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09653.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (40 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09677.pow 1)))

@[irreducible]
def a09679 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a09678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09654 ^ 1)
theorem ha09679 : a09679.IsHomogeneous 112 := by
  unfold a09679
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha09678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09654.pow 1)))

@[irreducible]
def a09680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a02484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01074 ^ 1 * a01702 ^ 1)
theorem ha09680 : a09680.IsHomogeneous 94 := by
  unfold a09680
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha02484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01074.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a05025 ^ 1)
theorem ha09681 : a09681.IsHomogeneous 95 := by
  unfold a09681
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02484.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha05025.pow 1)))

@[irreducible]
def a09682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09680 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09681 ^ 1)
theorem ha09682 : a09682.IsHomogeneous 95 := by
  unfold a09682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09681.pow 1)))

@[irreducible]
def a09683 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09616 ^ 1)
theorem ha09683 : a09683.IsHomogeneous 44 := by
  unfold a09683
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09606.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09616.pow 1)))

@[irreducible]
def a09684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09683 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09627 ^ 1)
theorem ha09684 : a09684.IsHomogeneous 44 := by
  unfold a09684
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09683.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09627.pow 1)))

@[irreducible]
def a09685 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a05025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a09684 ^ 1)
theorem ha09685 : a09685.IsHomogeneous 89 := by
  unfold a09685
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha05025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha09684.pow 1)))

@[irreducible]
def a09686 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09685 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09681 ^ 1)
theorem ha09686 : a09686.IsHomogeneous 95 := by
  unfold a09686
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09685.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09681.pow 1)))

@[irreducible]
def a09687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09682 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09686 ^ 1)
theorem ha09687 : a09687.IsHomogeneous 95 := by
  unfold a09687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09682.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09686.pow 1)))

@[irreducible]
def a09688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01074 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00384 ^ 1 * a03562 ^ 1)
theorem ha09688 : a09688.IsHomogeneous 94 := by
  unfold a09688
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01074.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00384.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a09689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09680 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09688 ^ 1)
theorem ha09689 : a09689.IsHomogeneous 94 := by
  unfold a09689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09688.pow 1)))

@[irreducible]
def a09690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09682 ^ 1)
theorem ha09690 : a09690.IsHomogeneous 95 := by
  unfold a09690
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09682.pow 1)))

@[irreducible]
def a09691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09690 ^ 1)
theorem ha09691 : a09691.IsHomogeneous 95 := by
  unfold a09691
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09690.pow 1)))

@[irreducible]
def a09692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02799 ^ 1)
theorem ha09692 : a09692.IsHomogeneous 94 := by
  unfold a09692
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a09693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00473 ^ 1 * a01678 ^ 1)
theorem ha09693 : a09693.IsHomogeneous 95 := by
  unfold a09693
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha01253.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00473.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09693 ^ 1)
theorem ha09694 : a09694.IsHomogeneous 95 := by
  unfold a09694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09692.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09693.pow 1)))

@[irreducible]
def a09695 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a05536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02799 ^ 1)
theorem ha09695 : a09695.IsHomogeneous 94 := by
  unfold a09695
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha05536.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a09696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09695 ^ 1)
theorem ha09696 : a09696.IsHomogeneous 94 := by
  unfold a09696
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09692.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09695.pow 1)))

@[irreducible]
def a09697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09696 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09694 ^ 1)
theorem ha09697 : a09697.IsHomogeneous 95 := by
  unfold a09697
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09696.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09694.pow 1)))

@[irreducible]
def a09698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00144 ^ 1 * a03534 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00473 ^ 1 * a01678 ^ 1)
theorem ha09698 : a09698.IsHomogeneous 89 := by
  unfold a09698
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00144.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00473.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09693 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09698 ^ 1)
theorem ha09699 : a09699.IsHomogeneous 95 := by
  unfold a09699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09693.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09698.pow 1)))

@[irreducible]
def a09700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09699 ^ 1)
theorem ha09700 : a09700.IsHomogeneous 95 := by
  unfold a09700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09699.pow 1)))

@[irreducible]
def a09701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09700 ^ 1)
theorem ha09701 : a09701.IsHomogeneous 95 := by
  unfold a09701
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09700.pow 1)))

@[irreducible]
def a09702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09691 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a09701 ^ 1)
theorem ha09702 : a09702.IsHomogeneous 95 := by
  unfold a09702
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09691.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha09701.pow 1)))

@[irreducible]
def a09703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09653 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a09702 ^ 1)
theorem ha09703 : a09703.IsHomogeneous 112 := by
  unfold a09703
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09653.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09702.pow 1)))

@[irreducible]
def a09704 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a09703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09679 ^ 1)
theorem ha09704 : a09704.IsHomogeneous 112 := by
  unfold a09704
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha09703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09679.pow 1)))

@[irreducible]
def a09705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a05039 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a09704 ^ 1)
theorem ha09705 : a09705.IsHomogeneous 130 := by
  unfold a09705
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha05039.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha09704.pow 1)))

@[irreducible]
def a09706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09586 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09705 ^ 1)
theorem ha09706 : a09706.IsHomogeneous 130 := by
  unfold a09706
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09705.pow 1)))

@[irreducible]
def a09707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09706 ^ 1)
theorem ha09707 : a09707.IsHomogeneous 130 := by
  unfold a09707
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09706.pow 1)))

@[irreducible]
def a09708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09707 ^ 1)
theorem ha09708 : a09708.IsHomogeneous 130 := by
  unfold a09708
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09707.pow 1)))

@[irreducible]
def a09709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a09708 ^ 1) + (C ((1 : ℂ) / (600 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a09584 ^ 1)
theorem ha09709 : a09709.IsHomogeneous 136 := by
  unfold a09709
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha09708.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (600 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha09584.pow 1)))

@[irreducible]
def a09710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05043 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a09709 ^ 1)
theorem ha09710 : a09710.IsHomogeneous 142 := by
  unfold a09710
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha09709.pow 1)))

@[irreducible]
def a09711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09558 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09710 ^ 1)
theorem ha09711 : a09711.IsHomogeneous 148 := by
  unfold a09711
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09710.pow 1)))

@[irreducible]
def a09712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09711 ^ 1)
theorem ha09712 : a09712.IsHomogeneous 148 := by
  unfold a09712
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09711.pow 1)))

@[irreducible]
def a09713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09712 ^ 1)
theorem ha09713 : a09713.IsHomogeneous 148 := by
  unfold a09713
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09712.pow 1)))

@[irreducible]
def a09714 : Poly := (C ((-3 : ℂ) / (1280 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a09556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a09713 ^ 1)
theorem ha09714 : a09714.IsHomogeneous 166 := by
  unfold a09714
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1280 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha09556.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha09713.pow 1)))

@[irreducible]
def a09715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a09714 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a05047 ^ 1)
theorem ha09715 : a09715.IsHomogeneous 196 := by
  unfold a09715
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha09714.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha05047.pow 1)))

@[irreducible]
def a09716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09715 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00014 ^ 1 * a09491 ^ 1)
theorem ha09716 : a09716.IsHomogeneous 196 := by
  unfold a09716
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09715.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00014.pow 1)).mul (ha09491.pow 1)))

@[irreducible]
def a09717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09716 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00014 ^ 1 * a09492 ^ 1)
theorem ha09717 : a09717.IsHomogeneous 196 := by
  unfold a09717
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00014.pow 1)).mul (ha09492.pow 1)))

@[irreducible]
def a09718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09717 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00014 ^ 1 * a09495 ^ 1)
theorem ha09718 : a09718.IsHomogeneous 196 := by
  unfold a09718
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00014.pow 1)).mul (ha09495.pow 1)))

@[irreducible]
def a09719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09718 ^ 1) + (C ((3 : ℂ) / (64 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a09489 ^ 1)
theorem ha09719 : a09719.IsHomogeneous 196 := by
  unfold a09719
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09718.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (64 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha09489.pow 1)))

@[irreducible]
def a09720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01284 ^ 1 * a01290 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02851 ^ 1)
theorem ha09720 : a09720.IsHomogeneous 446 := by
  unfold a09720
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01284.pow 1)).mul (ha01290.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a09721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a02860 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01284 ^ 1 * a01290 ^ 1)
theorem ha09721 : a09721.IsHomogeneous 470 := by
  unfold a09721
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha02860.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01284.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a09722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09721 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09720 ^ 1)
theorem ha09722 : a09722.IsHomogeneous 470 := by
  unfold a09722
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09720.pow 1)))

@[irreducible]
def a09723 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a05615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a02851 ^ 1)
theorem ha09723 : a09723.IsHomogeneous 386 := by
  unfold a09723
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha05615.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a09724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09720 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09723 ^ 1)
theorem ha09724 : a09724.IsHomogeneous 446 := by
  unfold a09724
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09720.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09723.pow 1)))

@[irreducible]
def a09725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09722 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09724 ^ 1)
theorem ha09725 : a09725.IsHomogeneous 470 := by
  unfold a09725
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09724.pow 1)))

@[irreducible]
def a09726 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a02860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a05627 ^ 1)
theorem ha09726 : a09726.IsHomogeneous 494 := by
  unfold a09726
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha02860.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha05627.pow 1)))

@[irreducible]
def a09727 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a09721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09726 ^ 1)
theorem ha09727 : a09727.IsHomogeneous 494 := by
  unfold a09727
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha09721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09726.pow 1)))

end CycleQ2Concrete
