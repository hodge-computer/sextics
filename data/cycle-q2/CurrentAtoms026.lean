import Proposal.CurrentAtoms025

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a08448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08447 ^ 1) + (C ((1 : ℂ) / (100 : ℂ)) * a00001 ^ 11 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 9 * a00100 ^ 6 * a08441 ^ 1)
theorem ha08448 : a08448.IsHomogeneous 329 := by
  unfold a08448
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08447.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (100 : ℂ))).mul (ha00001.pow 11)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 9)).mul (ha00100.pow 6)).mul (ha08441.pow 1)))

@[irreducible]
def a08449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08448 ^ 1)
theorem ha08449 : a08449.IsHomogeneous 329 := by
  unfold a08449
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08448.pow 1)))

@[irreducible]
def a08450 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a08449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a04328 ^ 1)
theorem ha08450 : a08450.IsHomogeneous 887 := by
  unfold a08450
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha08449.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha04328.pow 1)))

@[irreducible]
def a08451 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 5 * a00126 ^ 1 * a08450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 2 * a08431 ^ 1)
theorem ha08451 : a08451.IsHomogeneous 1083 := by
  unfold a08451
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha00126.pow 1)).mul (ha08450.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 2)).mul (ha08431.pow 1)))

@[irreducible]
def a08452 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a04499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a02203 ^ 1)
theorem ha08452 : a08452.IsHomogeneous 1421 := by
  unfold a08452
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha04499.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha02203.pow 1)))

@[irreducible]
def a08453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a08451 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00042 ^ 4 * a08452 ^ 1)
theorem ha08453 : a08453.IsHomogeneous 1536 := by
  unfold a08453
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha08451.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00042.pow 4)).mul (ha08452.pow 1)))

@[irreducible]
def a08454 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00937 ^ 1 * a02376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01026 ^ 1 * a02116 ^ 1)
theorem ha08454 : a08454.IsHomogeneous 1901 := by
  unfold a08454
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00937.pow 1)).mul (ha02376.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01026.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a08455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a08453 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00042 ^ 3 * a08454 ^ 1)
theorem ha08455 : a08455.IsHomogeneous 1989 := by
  unfold a08455
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha08453.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 3)).mul (ha08454.pow 1)))

@[irreducible]
def a08456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a04256 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a01180 ^ 1 * a02118 ^ 1)
theorem ha08456 : a08456.IsHomogeneous 2388 := by
  unfold a08456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha04256.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha01180.pow 1)).mul (ha02118.pow 1)))

@[irreducible]
def a08457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00042 ^ 2 * a08456 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a08455 ^ 1)
theorem ha08457 : a08457.IsHomogeneous 2442 := by
  unfold a08457
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00042.pow 2)).mul (ha08456.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha08455.pow 1)))

@[irreducible]
def a08458 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a04337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a02121 ^ 1)
theorem ha08458 : a08458.IsHomogeneous 690 := by
  unfold a08458
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha04337.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha02121.pow 1)))

@[irreducible]
def a08459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a02119 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a04333 ^ 1)
theorem ha08459 : a08459.IsHomogeneous 150 := by
  unfold a08459
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha02119.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha04333.pow 1)))

@[irreducible]
def a08460 : Poly := (C ((-3 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00595 ^ 1) + (C ((-1 : ℂ) / (1600 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00558 ^ 1) + (C ((1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00691 ^ 1)
theorem ha08460 : a08460.IsHomogeneous 80 := by
  unfold a08460
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00595.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1600 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00712.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00558.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a08461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00125 ^ 1 * a08460 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a04333 ^ 1)
theorem ha08461 : a08461.IsHomogeneous 150 := by
  unfold a08461
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00125.pow 1)).mul (ha08460.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha04333.pow 1)))

@[irreducible]
def a08462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08461 ^ 1)
theorem ha08462 : a08462.IsHomogeneous 150 := by
  unfold a08462
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08459.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08461.pow 1)))

@[irreducible]
def a08463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00713 ^ 1 * a02120 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a04335 ^ 1)
theorem ha08463 : a08463.IsHomogeneous 158 := by
  unfold a08463
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00713.pow 1)).mul (ha02120.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha04335.pow 1)))

@[irreducible]
def a08464 : Poly := (C ((-1 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00595 ^ 1) + (C ((1 : ℂ) / (200 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00712 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1)
theorem ha08464 : a08464.IsHomogeneous 78 := by
  unfold a08464
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00595.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (200 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00712.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a08465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a08464 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a04335 ^ 1)
theorem ha08465 : a08465.IsHomogeneous 158 := by
  unfold a08465
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha08464.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha04335.pow 1)))

@[irreducible]
def a08466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08465 ^ 1)
theorem ha08466 : a08466.IsHomogeneous 158 := by
  unfold a08466
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08465.pow 1)))

@[irreducible]
def a08467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08466 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a08462 ^ 1)
theorem ha08467 : a08467.IsHomogeneous 158 := by
  unfold a08467
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08466.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08462.pow 1)))

@[irreducible]
def a08468 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a04337 ^ 1)
theorem ha08468 : a08468.IsHomogeneous 436 := by
  unfold a08468
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08467.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha04337.pow 1)))

@[irreducible]
def a08469 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08468 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08458 ^ 1)
theorem ha08469 : a08469.IsHomogeneous 690 := by
  unfold a08469
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08468.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08458.pow 1)))

@[irreducible]
def a08470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a04338 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a08469 ^ 1)
theorem ha08470 : a08470.IsHomogeneous 769 := by
  unfold a08470
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha04338.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha08469.pow 1)))

@[irreducible]
def a08471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a02121 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a04338 ^ 1)
theorem ha08471 : a08471.IsHomogeneous 594 := by
  unfold a08471
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha02121.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha04338.pow 1)))

@[irreducible]
def a08472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08471 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a08470 ^ 1)
theorem ha08472 : a08472.IsHomogeneous 848 := by
  unfold a08472
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08471.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha08470.pow 1)))

@[irreducible]
def a08473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a04339 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08472 ^ 1)
theorem ha08473 : a08473.IsHomogeneous 956 := by
  unfold a08473
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha04339.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08472.pow 1)))

@[irreducible]
def a08474 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a04339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a02121 ^ 1)
theorem ha08474 : a08474.IsHomogeneous 713 := by
  unfold a08474
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha04339.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha02121.pow 1)))

@[irreducible]
def a08475 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a08473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08474 ^ 1)
theorem ha08475 : a08475.IsHomogeneous 1046 := by
  unfold a08475
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08473.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08474.pow 1)))

@[irreducible]
def a08476 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a04520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a02213 ^ 1)
theorem ha08476 : a08476.IsHomogeneous 1066 := by
  unfold a08476
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha04520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a08477 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01290 ^ 1)
theorem ha08477 : a08477.IsHomogeneous 793 := by
  unfold a08477
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a08478 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08476 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08477 ^ 1)
theorem ha08478 : a08478.IsHomogeneous 1126 := by
  unfold a08478
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08476.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08477.pow 1)))

@[irreducible]
def a08479 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a04520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a02213 ^ 1)
theorem ha08479 : a08479.IsHomogeneous 1006 := by
  unfold a08479
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha04520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a08480 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01313 ^ 1)
theorem ha08480 : a08480.IsHomogeneous 709 := by
  unfold a08480
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a08481 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08480 ^ 1)
theorem ha08481 : a08481.IsHomogeneous 1042 := by
  unfold a08481
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08479.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08480.pow 1)))

@[irreducible]
def a08482 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01103 ^ 1)
theorem ha08482 : a08482.IsHomogeneous 1126 := by
  unfold a08482
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02540 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01035 ^ 1 * a01103 ^ 1)
theorem ha08483 : a08483.IsHomogeneous 853 := by
  unfold a08483
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02540.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08483 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08482 ^ 1)
theorem ha08484 : a08484.IsHomogeneous 1186 := by
  unfold a08484
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08483.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08482.pow 1)))

@[irreducible]
def a08485 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01118 ^ 1)
theorem ha08485 : a08485.IsHomogeneous 1042 := by
  unfold a08485
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a08486 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a01035 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02574 ^ 1)
theorem ha08486 : a08486.IsHomogeneous 745 := by
  unfold a08486
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01118.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a08487 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08486 ^ 1)
theorem ha08487 : a08487.IsHomogeneous 1078 := by
  unfold a08487
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08485.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08486.pow 1)))

@[irreducible]
def a08488 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00988 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02308 ^ 1)
theorem ha08488 : a08488.IsHomogeneous 1188 := by
  unfold a08488
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00988.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a04713 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a02308 ^ 1)
theorem ha08489 : a08489.IsHomogeneous 915 := by
  unfold a08489
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha04713.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08489 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08488 ^ 1)
theorem ha08490 : a08490.IsHomogeneous 1248 := by
  unfold a08490
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08489.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08488.pow 1)))

@[irreducible]
def a08491 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00996 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02327 ^ 1)
theorem ha08491 : a08491.IsHomogeneous 1080 := by
  unfold a08491
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00996.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a08492 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a02327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a04754 ^ 1)
theorem ha08492 : a08492.IsHomogeneous 783 := by
  unfold a08492
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02327.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha04754.pow 1)))

@[irreducible]
def a08493 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08492 ^ 1)
theorem ha08493 : a08493.IsHomogeneous 1116 := by
  unfold a08493
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08491.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08492.pow 1)))

@[irreducible]
def a08494 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a04445 ^ 1)
theorem ha08494 : a08494.IsHomogeneous 1242 := by
  unfold a08494
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02173.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha04445.pow 1)))

@[irreducible]
def a08495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a04444 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02173 ^ 1)
theorem ha08495 : a08495.IsHomogeneous 507 := by
  unfold a08495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha04444.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02173.pow 1)))

@[irreducible]
def a08496 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00303 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00511 ^ 1)
theorem ha08496 : a08496.IsHomogeneous 120 := by
  unfold a08496
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00303.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00511.pow 1)))

@[irreducible]
def a08497 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00303 ^ 1)
theorem ha08497 : a08497.IsHomogeneous 120 := by
  unfold a08497
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00823.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00303.pow 1)))

@[irreducible]
def a08498 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a08497 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08496 ^ 1)
theorem ha08498 : a08498.IsHomogeneous 120 := by
  unfold a08498
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha08497.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08496.pow 1)))

@[irreducible]
def a08499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a08498 ^ 1) + (C ((675 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02419 ^ 1)
theorem ha08499 : a08499.IsHomogeneous 159 := by
  unfold a08499
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha08498.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((675 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02419.pow 1)))

@[irreducible]
def a08500 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a01041 ^ 1 * a01083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00389 ^ 1 * a02413 ^ 1)
theorem ha08500 : a08500.IsHomogeneous 162 := by
  unfold a08500
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).mul (ha01083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00389.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a08501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a02499 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a01041 ^ 1 * a01083 ^ 1)
theorem ha08501 : a08501.IsHomogeneous 162 := by
  unfold a08501
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha02499.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha01041.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a08502 : Poly := (C ((-45 : ℂ) / (4 : ℂ)) * a08501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08500 ^ 1)
theorem ha08502 : a08502.IsHomogeneous 162 := by
  unfold a08502
  exact (((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (4 : ℂ))).mul (ha08501.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08500.pow 1)))

@[irreducible]
def a08503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a08499 ^ 1) + (C ((100 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00002 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a08502 ^ 1)
theorem ha08503 : a08503.IsHomogeneous 171 := by
  unfold a08503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha08499.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((100 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha08502.pow 1)))

@[irreducible]
def a08504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02282 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00976 ^ 1 * a01207 ^ 1)
theorem ha08504 : a08504.IsHomogeneous 169 := by
  unfold a08504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02282.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00976.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a08505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a04661 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00455 ^ 1 * a02282 ^ 1)
theorem ha08505 : a08505.IsHomogeneous 169 := by
  unfold a08505
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha04661.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)).mul (ha02282.pow 1)))

@[irreducible]
def a08506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08504 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a08505 ^ 1)
theorem ha08506 : a08506.IsHomogeneous 169 := by
  unfold a08506
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha08505.pow 1)))

@[irreducible]
def a08507 : Poly := (C ((-3600 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a08506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08503 ^ 1)
theorem ha08507 : a08507.IsHomogeneous 171 := by
  unfold a08507
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3600 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha08506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08503.pow 1)))

@[irreducible]
def a08508 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a02159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04415 ^ 1)
theorem ha08508 : a08508.IsHomogeneous 177 := by
  unfold a08508
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha02159.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04415.pow 1)))

@[irreducible]
def a08509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a04355 ^ 1)
theorem ha08509 : a08509.IsHomogeneous 36 := by
  unfold a08509
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha04355.pow 1)))

@[irreducible]
def a08510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00506 ^ 1)
theorem ha08510 : a08510.IsHomogeneous 12 := by
  unfold a08510
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a08511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00316 ^ 1)
theorem ha08511 : a08511.IsHomogeneous 6 := by
  unfold a08511
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)))

@[irreducible]
def a08512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08511 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08510 ^ 1)
theorem ha08512 : a08512.IsHomogeneous 12 := by
  unfold a08512
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08511.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08510.pow 1)))

@[irreducible]
def a08513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02425 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08512 ^ 1)
theorem ha08513 : a08513.IsHomogeneous 40 := by
  unfold a08513
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02425.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08512.pow 1)))

@[irreducible]
def a08514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08513 ^ 1) + (C ((1 : ℂ) / (90 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08512 ^ 1)
theorem ha08514 : a08514.IsHomogeneous 40 := by
  unfold a08514
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08513.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (90 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08512.pow 1)))

@[irreducible]
def a08515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a04355 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a08514 ^ 1)
theorem ha08515 : a08515.IsHomogeneous 46 := by
  unfold a08515
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha04355.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha08514.pow 1)))

@[irreducible]
def a08516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a08509 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a08515 ^ 1)
theorem ha08516 : a08516.IsHomogeneous 46 := by
  unfold a08516
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha08509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha08515.pow 1)))

@[irreducible]
def a08517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00510 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00156 ^ 1)
theorem ha08517 : a08517.IsHomogeneous 18 := by
  unfold a08517
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00156 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha08518 : a08518.IsHomogeneous 12 := by
  unfold a08518
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00156.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a08519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a00316 ^ 1)
theorem ha08519 : a08519.IsHomogeneous 12 := by
  unfold a08519
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a08520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08517 ^ 1)
theorem ha08520 : a08520.IsHomogeneous 18 := by
  unfold a08520
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08519.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08518.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08517.pow 1)))

@[irreducible]
def a08521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08520 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02431 ^ 1)
theorem ha08521 : a08521.IsHomogeneous 37 := by
  unfold a08521
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08520.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02431.pow 1)))

@[irreducible]
def a08522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08521 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08520 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02431 ^ 1)
theorem ha08522 : a08522.IsHomogeneous 37 := by
  unfold a08522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08521.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08520.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02431.pow 1)))

@[irreducible]
def a08523 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a08522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08516 ^ 1)
theorem ha08523 : a08523.IsHomogeneous 46 := by
  unfold a08523
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08516.pow 1)))

@[irreducible]
def a08524 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a08523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04360 ^ 1)
theorem ha08524 : a08524.IsHomogeneous 82 := by
  unfold a08524
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha08523.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04360.pow 1)))

@[irreducible]
def a08525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00260 ^ 1 * a04360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a02129 ^ 1)
theorem ha08525 : a08525.IsHomogeneous 120 := by
  unfold a08525
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04360.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha02129.pow 1)))

@[irreducible]
def a08526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a08524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08525 ^ 1)
theorem ha08526 : a08526.IsHomogeneous 120 := by
  unfold a08526
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha08524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08525.pow 1)))

@[irreducible]
def a08527 : Poly := (C ((-108 : ℂ) / (5 : ℂ)) * a00484 ^ 1 * a02236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a04575 ^ 1)
theorem ha08527 : a08527.IsHomogeneous 126 := by
  unfold a08527
  exact ((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (5 : ℂ))).mul (ha00484.pow 1)).mul (ha02236.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha04575.pow 1)))

@[irreducible]
def a08528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00484 ^ 1 * a02236 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00950 ^ 1 * a01275 ^ 1)
theorem ha08528 : a08528.IsHomogeneous 128 := by
  unfold a08528
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00484.pow 1)).mul (ha02236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00950.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a08529 : Poly := (C ((-108 : ℂ) / (5 : ℂ)) * a08528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a08527 ^ 1)
theorem ha08529 : a08529.IsHomogeneous 128 := by
  unfold a08529
  exact (((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (5 : ℂ))).mul (ha08528.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha08527.pow 1)))

@[irreducible]
def a08530 : Poly := (C ((-3888 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a08526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a08529 ^ 1)
theorem ha08530 : a08530.IsHomogeneous 133 := by
  unfold a08530
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3888 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08526.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08529.pow 1)))

@[irreducible]
def a08531 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a01048 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a02432 ^ 1)
theorem ha08531 : a08531.IsHomogeneous 130 := by
  unfold a08531
  exact ((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha01048.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha02432.pow 1)))

@[irreducible]
def a08532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01048 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00370 ^ 1 * a02520 ^ 1)
theorem ha08532 : a08532.IsHomogeneous 133 := by
  unfold a08532
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01048.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00370.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a08533 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a08532 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a08531 ^ 1)
theorem ha08533 : a08533.IsHomogeneous 133 := by
  unfold a08533
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha08532.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha08531.pow 1)))

@[irreducible]
def a08534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08530 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a08533 ^ 1)
theorem ha08534 : a08534.IsHomogeneous 133 := by
  unfold a08534
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha08533.pow 1)))

@[irreducible]
def a08535 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00982 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a02295 ^ 1)
theorem ha08535 : a08535.IsHomogeneous 144 := by
  unfold a08535
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00982.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08536 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00137 ^ 1 * a04689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a02295 ^ 1)
theorem ha08536 : a08536.IsHomogeneous 153 := by
  unfold a08536
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00137.pow 1)).mul (ha04689.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08536 ^ 1)
theorem ha08537 : a08537.IsHomogeneous 153 := by
  unfold a08537
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08536.pow 1)))

@[irreducible]
def a08538 : Poly := (C ((-5 : ℂ) / (5184 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 2 * a08534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08537 ^ 1)
theorem ha08538 : a08538.IsHomogeneous 153 := by
  unfold a08538
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (5184 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08537.pow 1)))

@[irreducible]
def a08539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02158 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a04413 ^ 1)
theorem ha08539 : a08539.IsHomogeneous 129 := by
  unfold a08539
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha04413.pow 1)))

@[irreducible]
def a08540 : Poly := (C ((-1 : ℂ) / (2160 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00782 ^ 1)
theorem ha08540 : a08540.IsHomogeneous 15 := by
  unfold a08540
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2160 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00782.pow 1)))

@[irreducible]
def a08541 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a08540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a04368 ^ 1)
theorem ha08541 : a08541.IsHomogeneous 111 := by
  unfold a08541
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08540.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha04368.pow 1)))

@[irreducible]
def a08542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00301 ^ 1 * a04368 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00819 ^ 1 * a02133 ^ 1)
theorem ha08542 : a08542.IsHomogeneous 121 := by
  unfold a08542
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha04368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00819.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a08543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a08541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08542 ^ 1)
theorem ha08543 : a08543.IsHomogeneous 121 := by
  unfold a08543
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha08541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08542.pow 1)))

@[irreducible]
def a08544 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a04588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a02242 ^ 1)
theorem ha08544 : a08544.IsHomogeneous 125 := by
  unfold a08544
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha04588.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a08545 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00953 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00476 ^ 1 * a02242 ^ 1)
theorem ha08545 : a08545.IsHomogeneous 133 := by
  unfold a08545
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00953.pow 1)).mul (ha01258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a08546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08544 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08545 ^ 1)
theorem ha08546 : a08546.IsHomogeneous 133 := by
  unfold a08546
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08545.pow 1)))

@[irreducible]
def a08547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08546 ^ 1) + (C ((3 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a08543 ^ 1)
theorem ha08547 : a08547.IsHomogeneous 133 := by
  unfold a08547
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08546.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha08543.pow 1)))

@[irreducible]
def a08548 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a02441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01052 ^ 1 * a01079 ^ 1)
theorem ha08548 : a08548.IsHomogeneous 119 := by
  unfold a08548
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha02441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01052.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a08549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a01052 ^ 1 * a01079 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a02493 ^ 1)
theorem ha08549 : a08549.IsHomogeneous 127 := by
  unfold a08549
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha01052.pow 1)).mul (ha01079.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02493.pow 1)))

@[irreducible]
def a08550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08549 ^ 1)
theorem ha08550 : a08550.IsHomogeneous 127 := by
  unfold a08550
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08549.pow 1)))

@[irreducible]
def a08551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08547 ^ 1)
theorem ha08551 : a08551.IsHomogeneous 133 := by
  unfold a08551
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08547.pow 1)))

@[irreducible]
def a08552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a02278 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00974 ^ 1 * a01228 ^ 1)
theorem ha08552 : a08552.IsHomogeneous 112 := by
  unfold a08552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha02278.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00974.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a08553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a02278 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00138 ^ 1 * a04655 ^ 1)
theorem ha08553 : a08553.IsHomogeneous 121 := by
  unfold a08553
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha02278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00138.pow 1)).mul (ha04655.pow 1)))

@[irreducible]
def a08554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08552 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08553 ^ 1)
theorem ha08554 : a08554.IsHomogeneous 121 := by
  unfold a08554
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08552.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08553.pow 1)))

@[irreducible]
def a08555 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08554 ^ 1)
theorem ha08555 : a08555.IsHomogeneous 135 := by
  unfold a08555
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08551.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08554.pow 1)))

@[irreducible]
def a08556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a04411 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a02157 ^ 1)
theorem ha08556 : a08556.IsHomogeneous 102 := by
  unfold a08556
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha04411.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha02157.pow 1)))

@[irreducible]
def a08557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04378 ^ 1)
theorem ha08557 : a08557.IsHomogeneous 73 := by
  unfold a08557
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04378.pow 1)))

@[irreducible]
def a08558 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00368 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01041 ^ 1)
theorem ha08558 : a08558.IsHomogeneous 18 := by
  unfold a08558
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00368.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a08559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02413 ^ 1)
theorem ha08559 : a08559.IsHomogeneous 18 := by
  unfold a08559
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02413.pow 1)))

@[irreducible]
def a08560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08559 ^ 1)
theorem ha08560 : a08560.IsHomogeneous 18 := by
  unfold a08560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08559.pow 1)))

@[irreducible]
def a08561 : Poly := (C ((-2 : ℂ) / (405 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08560 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02456 ^ 1)
theorem ha08561 : a08561.IsHomogeneous 33 := by
  unfold a08561
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08560.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02456.pow 1)))

@[irreducible]
def a08562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08561 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02456 ^ 1)
theorem ha08562 : a08562.IsHomogeneous 33 := by
  unfold a08562
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08561.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02456.pow 1)))

@[irreducible]
def a08563 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a04378 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00100 ^ 1 * a08562 ^ 1)
theorem ha08563 : a08563.IsHomogeneous 73 := by
  unfold a08563
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha04378.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00100.pow 1)).mul (ha08562.pow 1)))

@[irreducible]
def a08564 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a08563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08557 ^ 1)
theorem ha08564 : a08564.IsHomogeneous 73 := by
  unfold a08564
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha08563.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08557.pow 1)))

@[irreducible]
def a08565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00958 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a02252 ^ 1)
theorem ha08565 : a08565.IsHomogeneous 91 := by
  unfold a08565
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00958.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a08566 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a04610 ^ 1)
theorem ha08566 : a08566.IsHomogeneous 91 := by
  unfold a08566
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02252.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha04610.pow 1)))

@[irreducible]
def a08567 : Poly := (C ((-9 : ℂ) / (10 : ℂ)) * a08566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08565 ^ 1)
theorem ha08567 : a08567.IsHomogeneous 91 := by
  unfold a08567
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (10 : ℂ))).mul (ha08566.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08565.pow 1)))

@[irreducible]
def a08568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08567 ^ 1) + (C ((27 : ℂ) / (50 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08564 ^ 1)
theorem ha08568 : a08568.IsHomogeneous 91 := by
  unfold a08568
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08567.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (50 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08564.pow 1)))

@[irreducible]
def a08569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00375 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01060 ^ 1)
theorem ha08569 : a08569.IsHomogeneous 91 := by
  unfold a08569
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00375.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a08570 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a02461 ^ 1)
theorem ha08570 : a08570.IsHomogeneous 91 := by
  unfold a08570
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01060.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha02461.pow 1)))

@[irreducible]
def a08571 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a08570 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08569 ^ 1)
theorem ha08571 : a08571.IsHomogeneous 91 := by
  unfold a08571
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha08570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08569.pow 1)))

@[irreducible]
def a08572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08568 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a08571 ^ 1)
theorem ha08572 : a08572.IsHomogeneous 91 := by
  unfold a08572
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha08571.pow 1)))

@[irreducible]
def a08573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00139 ^ 1 * a00595 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00465 ^ 1)
theorem ha08573 : a08573.IsHomogeneous 79 := by
  unfold a08573
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00139.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a08574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00046 ^ 1 * a01240 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00465 ^ 1)
theorem ha08574 : a08574.IsHomogeneous 79 := by
  unfold a08574
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00046.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a08575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08573 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a08574 ^ 1)
theorem ha08575 : a08575.IsHomogeneous 79 := by
  unfold a08575
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha08574.pow 1)))

@[irreducible]
def a08576 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08575 ^ 1)
theorem ha08576 : a08576.IsHomogeneous 93 := by
  unfold a08576
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08572.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08575.pow 1)))

@[irreducible]
def a08577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00558 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00173 ^ 1 * a00300 ^ 1)
theorem ha08577 : a08577.IsHomogeneous 91 := by
  unfold a08577
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00558.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00173.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a08578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00173 ^ 1 * a00300 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00039 ^ 1 * a00817 ^ 1)
theorem ha08578 : a08578.IsHomogeneous 85 := by
  unfold a08578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00173.pow 1)).mul (ha00300.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00039.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a08579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08577 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a08578 ^ 1)
theorem ha08579 : a08579.IsHomogeneous 91 := by
  unfold a08579
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha08578.pow 1)))

@[irreducible]
def a08580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08576 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a08579 ^ 1)
theorem ha08580 : a08580.IsHomogeneous 93 := by
  unfold a08580
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08576.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha08579.pow 1)))

@[irreducible]
def a08581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02144 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00260 ^ 1 * a04390 ^ 1)
theorem ha08581 : a08581.IsHomogeneous 79 := by
  unfold a08581
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00260.pow 1)).mul (ha04390.pow 1)))

@[irreducible]
def a08582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00511 ^ 1)
theorem ha08582 : a08582.IsHomogeneous 36 := by
  unfold a08582
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00511.pow 1)))

@[irreducible]
def a08583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00156 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00317 ^ 1)
theorem ha08583 : a08583.IsHomogeneous 27 := by
  unfold a08583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a08584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08582 ^ 1)
theorem ha08584 : a08584.IsHomogeneous 36 := by
  unfold a08584
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08582.pow 1)))

@[irreducible]
def a08585 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a08584 ^ 1)
theorem ha08585 : a08585.IsHomogeneous 42 := by
  unfold a08585
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02456.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha08584.pow 1)))

@[irreducible]
def a08586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08585 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a08560 ^ 1)
theorem ha08586 : a08586.IsHomogeneous 42 := by
  unfold a08586
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08585.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha08560.pow 1)))

@[irreducible]
def a08587 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a08586 ^ 1)
theorem ha08587 : a08587.IsHomogeneous 79 := by
  unfold a08587
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04390.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha08586.pow 1)))

@[irreducible]
def a08588 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a08587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08581 ^ 1)
theorem ha08588 : a08588.IsHomogeneous 79 := by
  unfold a08588
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha08587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08581.pow 1)))

@[irreducible]
def a08589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00963 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a02261 ^ 1)
theorem ha08589 : a08589.IsHomogeneous 91 := by
  unfold a08589
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha02261.pow 1)))

@[irreducible]
def a08590 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a04627 ^ 1)
theorem ha08590 : a08590.IsHomogeneous 91 := by
  unfold a08590
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02261.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha04627.pow 1)))

@[irreducible]
def a08591 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a08590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08589 ^ 1)
theorem ha08591 : a08591.IsHomogeneous 91 := by
  unfold a08591
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha08590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08589.pow 1)))

@[irreducible]
def a08592 : Poly := (C ((-25 : ℂ) / (18 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08588 ^ 1)
theorem ha08592 : a08592.IsHomogeneous 93 := by
  unfold a08592
  exact (((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (18 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08591.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08588.pow 1)))

@[irreducible]
def a08593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00379 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01067 ^ 1)
theorem ha08593 : a08593.IsHomogeneous 91 := by
  unfold a08593
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00379.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a08594 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a02474 ^ 1)
theorem ha08594 : a08594.IsHomogeneous 91 := by
  unfold a08594
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01067.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha02474.pow 1)))

@[irreducible]
def a08595 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a08594 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08593 ^ 1)
theorem ha08595 : a08595.IsHomogeneous 91 := by
  unfold a08595
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha08594.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08593.pow 1)))

@[irreducible]
def a08596 : Poly := (C ((-20 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08592 ^ 1)
theorem ha08596 : a08596.IsHomogeneous 93 := by
  unfold a08596
  exact (((((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08595.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08592.pow 1)))

@[irreducible]
def a08597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00141 ^ 1 * a00595 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00469 ^ 1)
theorem ha08597 : a08597.IsHomogeneous 79 := by
  unfold a08597
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00141.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a08598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00046 ^ 1 * a01248 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00469 ^ 1)
theorem ha08598 : a08598.IsHomogeneous 79 := by
  unfold a08598
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00046.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a08599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08597 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a08598 ^ 1)
theorem ha08599 : a08599.IsHomogeneous 79 := by
  unfold a08599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha08598.pow 1)))

@[irreducible]
def a08600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08596 ^ 1) + (C ((100 : ℂ) / (9 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08599 ^ 1)
theorem ha08600 : a08600.IsHomogeneous 93 := by
  unfold a08600
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08596.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((100 : ℂ) / (9 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08599.pow 1)))

@[irreducible]
def a08601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08600 ^ 1) + (C ((200 : ℂ) / (27 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a08579 ^ 1)
theorem ha08601 : a08601.IsHomogeneous 93 := by
  unfold a08601
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08600.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((200 : ℂ) / (27 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha08579.pow 1)))

@[irreducible]
def a08602 : Poly := (C ((-9 : ℂ) / (250 : ℂ)) * a08601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08580 ^ 1)
theorem ha08602 : a08602.IsHomogeneous 93 := by
  unfold a08602
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (250 : ℂ))).mul (ha08601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08580.pow 1)))

@[irreducible]
def a08603 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a08584 ^ 1)
theorem ha08603 : a08603.IsHomogeneous 42 := by
  unfold a08603
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02456.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha08584.pow 1)))

@[irreducible]
def a08604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08603 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a08560 ^ 1)
theorem ha08604 : a08604.IsHomogeneous 42 := by
  unfold a08604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08603.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha08560.pow 1)))

@[irreducible]
def a08605 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08604 ^ 1)
theorem ha08605 : a08605.IsHomogeneous 42 := by
  unfold a08605
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08604.pow 1)))

@[irreducible]
def a08606 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a08605 ^ 1)
theorem ha08606 : a08606.IsHomogeneous 79 := by
  unfold a08606
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04402.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha08605.pow 1)))

@[irreducible]
def a08607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02152 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00260 ^ 1 * a04402 ^ 1)
theorem ha08607 : a08607.IsHomogeneous 79 := by
  unfold a08607
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00260.pow 1)).mul (ha04402.pow 1)))

@[irreducible]
def a08608 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a08607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08606 ^ 1)
theorem ha08608 : a08608.IsHomogeneous 79 := by
  unfold a08608
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha08607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08606.pow 1)))

@[irreducible]
def a08609 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a04642 ^ 1)
theorem ha08609 : a08609.IsHomogeneous 91 := by
  unfold a08609
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02271.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha04642.pow 1)))

@[irreducible]
def a08610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00970 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a02271 ^ 1)
theorem ha08610 : a08610.IsHomogeneous 91 := by
  unfold a08610
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha02271.pow 1)))

@[irreducible]
def a08611 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a08610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08609 ^ 1)
theorem ha08611 : a08611.IsHomogeneous 91 := by
  unfold a08611
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha08610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08609.pow 1)))

@[irreducible]
def a08612 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08611 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08608 ^ 1)
theorem ha08612 : a08612.IsHomogeneous 93 := by
  unfold a08612
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08611.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08608.pow 1)))

@[irreducible]
def a08613 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a02484 ^ 1)
theorem ha08613 : a08613.IsHomogeneous 91 := by
  unfold a08613
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01074.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha02484.pow 1)))

@[irreducible]
def a08614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00384 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01074 ^ 1)
theorem ha08614 : a08614.IsHomogeneous 91 := by
  unfold a08614
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00384.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a08615 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a08614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08613 ^ 1)
theorem ha08615 : a08615.IsHomogeneous 91 := by
  unfold a08615
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha08614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08613.pow 1)))

@[irreducible]
def a08616 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08612 ^ 1)
theorem ha08616 : a08616.IsHomogeneous 93 := by
  unfold a08616
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08615.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08612.pow 1)))

@[irreducible]
def a08617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00046 ^ 1 * a01253 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00473 ^ 1)
theorem ha08617 : a08617.IsHomogeneous 79 := by
  unfold a08617
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00046.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a08618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00144 ^ 1 * a00595 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00473 ^ 1)
theorem ha08618 : a08618.IsHomogeneous 79 := by
  unfold a08618
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00144.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a08619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08617 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a08618 ^ 1)
theorem ha08619 : a08619.IsHomogeneous 79 := by
  unfold a08619
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08617.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha08618.pow 1)))

@[irreducible]
def a08620 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08619 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08616 ^ 1)
theorem ha08620 : a08620.IsHomogeneous 93 := by
  unfold a08620
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08616.pow 1)))

@[irreducible]
def a08621 : Poly := (C ((-10 : ℂ) / (9 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a08579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08620 ^ 1)
theorem ha08621 : a08621.IsHomogeneous 93 := by
  unfold a08621
  exact (((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (9 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha08579.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08620.pow 1)))

@[irreducible]
def a08622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08602 ^ 1) + (C ((2 : ℂ) / (25 : ℂ)) * a08621 ^ 1)
theorem ha08622 : a08622.IsHomogeneous 93 := by
  unfold a08622
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (25 : ℂ))).mul (ha08621.pow 1)))

@[irreducible]
def a08623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a04411 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a08622 ^ 1)
theorem ha08623 : a08623.IsHomogeneous 111 := by
  unfold a08623
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha04411.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha08622.pow 1)))

@[irreducible]
def a08624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08623 ^ 1)
theorem ha08624 : a08624.IsHomogeneous 111 := by
  unfold a08624
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08623.pow 1)))

@[irreducible]
def a08625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a08624 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a08555 ^ 1)
theorem ha08625 : a08625.IsHomogeneous 135 := by
  unfold a08625
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha08624.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha08555.pow 1)))

@[irreducible]
def a08626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04413 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a08625 ^ 1)
theorem ha08626 : a08626.IsHomogeneous 135 := by
  unfold a08626
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04413.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha08625.pow 1)))

@[irreducible]
def a08627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08539 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a08626 ^ 1)
theorem ha08627 : a08627.IsHomogeneous 135 := by
  unfold a08627
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha08626.pow 1)))

@[irreducible]
def a08628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08538 ^ 1) + (C ((125 : ℂ) / (27 : ℂ)) * a00014 ^ 3 * a08627 ^ 1)
theorem ha08628 : a08628.IsHomogeneous 153 := by
  unfold a08628
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08538.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (27 : ℂ))).mul (ha00014.pow 3)).mul (ha08627.pow 1)))

@[irreducible]
def a08629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a08628 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a04415 ^ 1)
theorem ha08629 : a08629.IsHomogeneous 183 := by
  unfold a08629
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha08628.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha04415.pow 1)))

@[irreducible]
def a08630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08629 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a08508 ^ 1)
theorem ha08630 : a08630.IsHomogeneous 183 := by
  unfold a08630
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08629.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha08508.pow 1)))

@[irreducible]
def a08631 : Poly := (C ((-1 : ℂ) / (243 : ℂ)) * a00014 ^ 2 * a08507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08630 ^ 1)
theorem ha08631 : a08631.IsHomogeneous 183 := by
  unfold a08631
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (243 : ℂ))).mul (ha00014.pow 2)).mul (ha08507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08630.pow 1)))

@[irreducible]
def a08632 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00988 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a02308 ^ 1)
theorem ha08632 : a08632.IsHomogeneous 479 := by
  unfold a08632
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00988.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a04713 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a02308 ^ 1)
theorem ha08633 : a08633.IsHomogeneous 503 := by
  unfold a08633
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha04713.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08633 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a08632 ^ 1)
theorem ha08634 : a08634.IsHomogeneous 503 := by
  unfold a08634
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08633.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha08632.pow 1)))

@[irreducible]
def a08635 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01099 ^ 1 * a01103 ^ 1)
theorem ha08635 : a08635.IsHomogeneous 458 := by
  unfold a08635
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01099.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a02540 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01099 ^ 1 * a01103 ^ 1)
theorem ha08636 : a08636.IsHomogeneous 482 := by
  unfold a08636
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha02540.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01099.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08636 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a08635 ^ 1)
theorem ha08637 : a08637.IsHomogeneous 482 := by
  unfold a08637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08636.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha08635.pow 1)))

@[irreducible]
def a08638 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a04706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a02304 ^ 1)
theorem ha08638 : a08638.IsHomogeneous 395 := by
  unfold a08638
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha04706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha02304.pow 1)))

@[irreducible]
def a08639 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00986 ^ 1 * a01290 ^ 1)
theorem ha08639 : a08639.IsHomogeneous 455 := by
  unfold a08639
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00986.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a08640 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08638 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08639 ^ 1)
theorem ha08640 : a08640.IsHomogeneous 455 := by
  unfold a08640
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08639.pow 1)))

@[irreducible]
def a08641 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00395 ^ 1 * a00506 ^ 1)
theorem ha08641 : a08641.IsHomogeneous 139 := by
  unfold a08641
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01097.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00395.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a08642 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a02530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01097 ^ 1)
theorem ha08642 : a08642.IsHomogeneous 139 := by
  unfold a08642
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha02530.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a08643 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a08642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08641 ^ 1)
theorem ha08643 : a08643.IsHomogeneous 139 := by
  unfold a08643
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha08642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08641.pow 1)))

@[irreducible]
def a08644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a02511 ^ 1) + (C ((5 : ℂ) / (1944 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a08643 ^ 1)
theorem ha08644 : a08644.IsHomogeneous 146 := by
  unfold a08644
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02511.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha08643.pow 1)))

@[irreducible]
def a08645 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00985 ^ 1)
theorem ha08645 : a08645.IsHomogeneous 142 := by
  unfold a08645
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00985.pow 1)))

@[irreducible]
def a08646 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04703 ^ 1)
theorem ha08646 : a08646.IsHomogeneous 148 := by
  unfold a08646
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02302.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04703.pow 1)))

@[irreducible]
def a08647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08646 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a08645 ^ 1)
theorem ha08647 : a08647.IsHomogeneous 148 := by
  unfold a08647
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08646.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha08645.pow 1)))

@[irreducible]
def a08648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08647 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08644 ^ 1)
theorem ha08648 : a08648.IsHomogeneous 148 := by
  unfold a08648
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08647.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08644.pow 1)))

@[irreducible]
def a08649 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a02170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a04439 ^ 1)
theorem ha08649 : a08649.IsHomogeneous 161 := by
  unfold a08649
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha02170.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha04439.pow 1)))

@[irreducible]
def a08650 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04430 ^ 1)
theorem ha08650 : a08650.IsHomogeneous 133 := by
  unfold a08650
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02166.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04430.pow 1)))

@[irreducible]
def a08651 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00173 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00558 ^ 1)
theorem ha08651 : a08651.IsHomogeneous 73 := by
  unfold a08651
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00173.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00558.pow 1)))

@[irreducible]
def a08652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00173 ^ 1 * a00260 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00039 ^ 1 * a00712 ^ 1)
theorem ha08652 : a08652.IsHomogeneous 73 := by
  unfold a08652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00173.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00039.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a08653 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a08652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08651 ^ 1)
theorem ha08653 : a08653.IsHomogeneous 73 := by
  unfold a08653
  exact (((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha08652.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08651.pow 1)))

@[irreducible]
def a08654 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00082 ^ 1 * a00595 ^ 1)
theorem ha08654 : a08654.IsHomogeneous 92 := by
  unfold a08654
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00082.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a08655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00046 ^ 1 * a00691 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00241 ^ 1)
theorem ha08655 : a08655.IsHomogeneous 92 := by
  unfold a08655
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00046.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a08656 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08654 ^ 1)
theorem ha08656 : a08656.IsHomogeneous 92 := by
  unfold a08656
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08654.pow 1)))

@[irreducible]
def a08657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08656 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a08653 ^ 1)
theorem ha08657 : a08657.IsHomogeneous 92 := by
  unfold a08657
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08656.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha08653.pow 1)))

@[irreducible]
def a08658 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a00637 ^ 1)
theorem ha08658 : a08658.IsHomogeneous 96 := by
  unfold a08658
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a08659 : Poly := (C ((-432 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a08658 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08657 ^ 1)
theorem ha08659 : a08659.IsHomogeneous 97 := by
  unfold a08659
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha08658.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08657.pow 1)))

@[irreducible]
def a08660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08656 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08659 ^ 1)
theorem ha08660 : a08660.IsHomogeneous 97 := by
  unfold a08660
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08659.pow 1)))

@[irreducible]
def a08661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08660 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08653 ^ 1)
theorem ha08661 : a08661.IsHomogeneous 97 := by
  unfold a08661
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08660.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08653.pow 1)))

@[irreducible]
def a08662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08661 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a04430 ^ 1)
theorem ha08662 : a08662.IsHomogeneous 133 := by
  unfold a08662
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08661.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha04430.pow 1)))

@[irreducible]
def a08663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08650 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a08662 ^ 1)
theorem ha08663 : a08663.IsHomogeneous 133 := by
  unfold a08663
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08650.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha08662.pow 1)))

@[irreducible]
def a08664 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02295 ^ 1)
theorem ha08664 : a08664.IsHomogeneous 142 := by
  unfold a08664
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04689 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a02295 ^ 1)
theorem ha08665 : a08665.IsHomogeneous 142 := by
  unfold a08665
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04689.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08664 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a08665 ^ 1)
theorem ha08666 : a08666.IsHomogeneous 142 := by
  unfold a08666
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08664.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha08665.pow 1)))

@[irreducible]
def a08667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a08663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a08666 ^ 1)
theorem ha08667 : a08667.IsHomogeneous 146 := by
  unfold a08667
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08663.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha08666.pow 1)))

@[irreducible]
def a08668 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00393 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01092 ^ 1)
theorem ha08668 : a08668.IsHomogeneous 145 := by
  unfold a08668
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00393.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a08669 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02520 ^ 1)
theorem ha08669 : a08669.IsHomogeneous 145 := by
  unfold a08669
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a08670 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a08669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08668 ^ 1)
theorem ha08670 : a08670.IsHomogeneous 145 := by
  unfold a08670
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha08669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08668.pow 1)))

@[irreducible]
def a08671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08667 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a08670 ^ 1)
theorem ha08671 : a08671.IsHomogeneous 146 := by
  unfold a08671
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08667.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha08670.pow 1)))

@[irreducible]
def a08672 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a00595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00484 ^ 1)
theorem ha08672 : a08672.IsHomogeneous 128 := by
  unfold a08672
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a08673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01275 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00484 ^ 1)
theorem ha08673 : a08673.IsHomogeneous 128 := by
  unfold a08673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a08674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08672 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a08673 ^ 1)
theorem ha08674 : a08674.IsHomogeneous 128 := by
  unfold a08674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha08673.pow 1)))

@[irreducible]
def a08675 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 2 * a08674 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08671 ^ 1)
theorem ha08675 : a08675.IsHomogeneous 146 := by
  unfold a08675
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08674.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08671.pow 1)))

@[irreducible]
def a08676 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00173 ^ 1 * a00260 ^ 1)
theorem ha08676 : a08676.IsHomogeneous 73 := by
  unfold a08676
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00173.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a08677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00829 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00173 ^ 1 * a00260 ^ 1)
theorem ha08677 : a08677.IsHomogeneous 109 := by
  unfold a08677
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00829.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00173.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a08678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08676 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a08677 ^ 1)
theorem ha08678 : a08678.IsHomogeneous 109 := by
  unfold a08678
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha08677.pow 1)))

@[irreducible]
def a08679 : Poly := (C ((-16 : ℂ) / (15 : ℂ)) * a00001 ^ 5 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 4 * a08678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08675 ^ 1)
theorem ha08679 : a08679.IsHomogeneous 146 := by
  unfold a08679
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (15 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha08678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08675.pow 1)))

@[irreducible]
def a08680 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a04439 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a08679 ^ 1)
theorem ha08680 : a08680.IsHomogeneous 170 := by
  unfold a08680
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha04439.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha08679.pow 1)))

@[irreducible]
def a08681 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08680 ^ 1)
theorem ha08681 : a08681.IsHomogeneous 170 := by
  unfold a08681
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08680.pow 1)))

@[irreducible]
def a08682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08681 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08648 ^ 1)
theorem ha08682 : a08682.IsHomogeneous 170 := by
  unfold a08682
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08681.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08648.pow 1)))

@[irreducible]
def a08683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08682 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a04441 ^ 1)
theorem ha08683 : a08683.IsHomogeneous 278 := by
  unfold a08683
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08682.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha04441.pow 1)))

@[irreducible]
def a08684 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a04441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a02171 ^ 1)
theorem ha08684 : a08684.IsHomogeneous 368 := by
  unfold a08684
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha04441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha02171.pow 1)))

@[irreducible]
def a08685 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a08683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08684 ^ 1)
theorem ha08685 : a08685.IsHomogeneous 368 := by
  unfold a08685
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08684.pow 1)))

@[irreducible]
def a08686 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00042 ^ 2 * a08640 ^ 1) + (C ((-1 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 1 * a08685 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a08634 ^ 1) + (C ((25 : ℂ) / (1728 : ℂ)) * a00000 ^ 1 * a00042 ^ 1 * a08637 ^ 1)
theorem ha08686 : a08686.IsHomogeneous 507 := by
  unfold a08686
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00042.pow 2)).mul (ha08640.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha08685.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha08634.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1728 : ℂ))).mul (ha00000.pow 1)).mul (ha00042.pow 1)).mul (ha08637.pow 1)))

@[irreducible]
def a08687 : Poly := (C ((-3 : ℂ) / (100 : ℂ)) * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00042 ^ 5 * a00100 ^ 5 * a08631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08686 ^ 1)
theorem ha08687 : a08687.IsHomogeneous 507 := by
  unfold a08687
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (100 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha08631.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08686.pow 1)))

@[irreducible]
def a08688 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a08687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a04444 ^ 1)
theorem ha08688 : a08688.IsHomogeneous 507 := by
  unfold a08688
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha08687.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha04444.pow 1)))

@[irreducible]
def a08689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08495 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08688 ^ 1)
theorem ha08689 : a08689.IsHomogeneous 507 := by
  unfold a08689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08495.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08688.pow 1)))

@[irreducible]
def a08690 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a04445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a08689 ^ 1)
theorem ha08690 : a08690.IsHomogeneous 933 := by
  unfold a08690
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha04445.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha08689.pow 1)))

@[irreducible]
def a08691 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a08494 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08690 ^ 1)
theorem ha08691 : a08691.IsHomogeneous 1266 := by
  unfold a08691
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha08494.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08690.pow 1)))

@[irreducible]
def a08692 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a04468 ^ 1)
theorem ha08692 : a08692.IsHomogeneous 1110 := by
  unfold a08692
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02183.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha04468.pow 1)))

@[irreducible]
def a08693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04467 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02183 ^ 1)
theorem ha08693 : a08693.IsHomogeneous 351 := by
  unfold a08693
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04467.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02183.pow 1)))

@[irreducible]
def a08694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a04451 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a02177 ^ 1)
theorem ha08694 : a08694.IsHomogeneous 58 := by
  unfold a08694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha04451.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha02177.pow 1)))

@[irreducible]
def a08695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00511 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00298 ^ 1)
theorem ha08695 : a08695.IsHomogeneous 42 := by
  unfold a08695
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00511.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a08696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha08696 : a08696.IsHomogeneous 36 := by
  unfold a08696
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a08697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08695 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08696 ^ 1)
theorem ha08697 : a08697.IsHomogeneous 42 := by
  unfold a08697
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08695.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08696.pow 1)))

@[irreducible]
def a08698 : Poly := (C ((-45 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a08697 ^ 1)
theorem ha08698 : a08698.IsHomogeneous 49 := by
  unfold a08698
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02549.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha08697.pow 1)))

@[irreducible]
def a08699 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a01041 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a02413 ^ 1)
theorem ha08699 : a08699.IsHomogeneous 24 := by
  unfold a08699
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01041.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a08700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08698 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a08699 ^ 1)
theorem ha08700 : a08700.IsHomogeneous 49 := by
  unfold a08700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08698.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha08699.pow 1)))

@[irreducible]
def a08701 : Poly := (C ((-45 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08700 ^ 1)
theorem ha08701 : a08701.IsHomogeneous 49 := by
  unfold a08701
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08700.pow 1)))

@[irreducible]
def a08702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a08697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08701 ^ 1)
theorem ha08702 : a08702.IsHomogeneous 49 := by
  unfold a08702
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha08697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08701.pow 1)))

@[irreducible]
def a08703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a04451 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a08702 ^ 1)
theorem ha08703 : a08703.IsHomogeneous 67 := by
  unfold a08703
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha04451.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha08702.pow 1)))

end CycleQ2Concrete
