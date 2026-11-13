import Proposal.CurrentAtoms013

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a05376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05374 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05375 ^ 1)
theorem ha05376 : a05376.IsHomogeneous 427 := by
  unfold a05376
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05374.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05375.pow 1)))

@[irreducible]
def a05377 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00491 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00151 ^ 1 * a03974 ^ 1)
theorem ha05377 : a05377.IsHomogeneous 427 := by
  unfold a05377
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00491.pow 1)).mul (ha01946.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha03974.pow 1)))

@[irreducible]
def a05378 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a05377 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05374 ^ 1)
theorem ha05378 : a05378.IsHomogeneous 427 := by
  unfold a05378
  exact (((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha05377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05374.pow 1)))

@[irreducible]
def a05379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05378 ^ 1)
theorem ha05379 : a05379.IsHomogeneous 427 := by
  unfold a05379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05378.pow 1)))

@[irreducible]
def a05380 : Poly := (C ((-25 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00823 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01923 ^ 1)
theorem ha05380 : a05380.IsHomogeneous 135 := by
  unfold a05380
  exact (((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00823.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a05381 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00823 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a02710 ^ 1)
theorem ha05381 : a05381.IsHomogeneous 132 := by
  unfold a05381
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00823.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05380 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a05381 ^ 1)
theorem ha05382 : a05382.IsHomogeneous 135 := by
  unfold a05382
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05380.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha05381.pow 1)))

@[irreducible]
def a05383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha05383 : a05383.IsHomogeneous 18 := by
  unfold a05383
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05383 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01352 ^ 1)
theorem ha05384 : a05384.IsHomogeneous 18 := by
  unfold a05384
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05383.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01352.pow 1)))

@[irreducible]
def a05385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01353 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a05384 ^ 1)
theorem ha05385 : a05385.IsHomogeneous 18 := by
  unfold a05385
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha05384.pow 1)))

@[irreducible]
def a05386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00864 ^ 1)
theorem ha05386 : a05386.IsHomogeneous 18 := by
  unfold a05386
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05383 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05386 ^ 1)
theorem ha05387 : a05387.IsHomogeneous 18 := by
  unfold a05387
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05386.pow 1)))

@[irreducible]
def a05388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05387 ^ 1)
theorem ha05388 : a05388.IsHomogeneous 18 := by
  unfold a05388
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05387.pow 1)))

@[irreducible]
def a05389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05385 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a05388 ^ 1)
theorem ha05389 : a05389.IsHomogeneous 18 := by
  unfold a05389
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha05388.pow 1)))

@[irreducible]
def a05390 : Poly := (C ((-7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a02710 ^ 1)
theorem ha05390 : a05390.IsHomogeneous 132 := by
  unfold a05390
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05390 ^ 1)
theorem ha05391 : a05391.IsHomogeneous 132 := by
  unfold a05391
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05390.pow 1)))

@[irreducible]
def a05392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05382 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a05391 ^ 1)
theorem ha05392 : a05392.IsHomogeneous 135 := by
  unfold a05392
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05382.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha05391.pow 1)))

@[irreducible]
def a05393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a03933 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 1 * a01923 ^ 1)
theorem ha05393 : a05393.IsHomogeneous 135 := by
  unfold a05393
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha03933.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a05394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05380 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a05393 ^ 1)
theorem ha05394 : a05394.IsHomogeneous 135 := by
  unfold a05394
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha05393.pow 1)))

@[irreducible]
def a05395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05382 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05394 ^ 1)
theorem ha05395 : a05395.IsHomogeneous 135 := by
  unfold a05395
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05382.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05394.pow 1)))

@[irreducible]
def a05396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05395 ^ 1)
theorem ha05396 : a05396.IsHomogeneous 135 := by
  unfold a05396
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05392.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05395.pow 1)))

@[irreducible]
def a05397 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00480 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a01264 ^ 1)
theorem ha05397 : a05397.IsHomogeneous 172 := by
  unfold a05397
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00480.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha01264.pow 1)))

@[irreducible]
def a05398 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00809 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02814 ^ 1)
theorem ha05398 : a05398.IsHomogeneous 179 := by
  unfold a05398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha01264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a05399 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05398 ^ 1)
theorem ha05399 : a05399.IsHomogeneous 179 := by
  unfold a05399
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05398.pow 1)))

@[irreducible]
def a05400 : Poly := (C ((-7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00148 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a01896 ^ 1)
theorem ha05400 : a05400.IsHomogeneous 166 := by
  unfold a05400
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a05401 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a05400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05397 ^ 1)
theorem ha05401 : a05401.IsHomogeneous 172 := by
  unfold a05401
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha05400.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05397.pow 1)))

@[irreducible]
def a05402 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05401 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05399 ^ 1)
theorem ha05402 : a05402.IsHomogeneous 179 := by
  unfold a05402
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05399.pow 1)))

@[irreducible]
def a05403 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00459 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00829 ^ 1 * a01223 ^ 1)
theorem ha05403 : a05403.IsHomogeneous 141 := by
  unfold a05403
  exact (((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00459.pow 1)).mul (ha01938.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00829.pow 1)).mul (ha01223.pow 1)))

@[irreducible]
def a05404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a02744 ^ 1)
theorem ha05404 : a05404.IsHomogeneous 135 := by
  unfold a05404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha01223.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02744.pow 1)))

@[irreducible]
def a05405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05403 ^ 1)
theorem ha05405 : a05405.IsHomogeneous 141 := by
  unfold a05405
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05403.pow 1)))

@[irreducible]
def a05406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a01213 ^ 1)
theorem ha05406 : a05406.IsHomogeneous 45 := by
  unfold a05406
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha01213.pow 1)))

@[irreducible]
def a05407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha05407 : a05407.IsHomogeneous 24 := by
  unfold a05407
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a05408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05407 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05406 ^ 1)
theorem ha05408 : a05408.IsHomogeneous 48 := by
  unfold a05408
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05407.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05406.pow 1)))

@[irreducible]
def a05409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01213 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a02724 ^ 1)
theorem ha05409 : a05409.IsHomogeneous 45 := by
  unfold a05409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha02724.pow 1)))

@[irreducible]
def a05410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05406 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a05409 ^ 1)
theorem ha05410 : a05410.IsHomogeneous 45 := by
  unfold a05410
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha05409.pow 1)))

@[irreducible]
def a05411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05408 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05410 ^ 1)
theorem ha05411 : a05411.IsHomogeneous 48 := by
  unfold a05411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05408.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05410.pow 1)))

@[irreducible]
def a05412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 2)
theorem ha05412 : a05412.IsHomogeneous 42 := by
  unfold a05412
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00865.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 2)))

@[irreducible]
def a05413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00865 ^ 1)
theorem ha05413 : a05413.IsHomogeneous 42 := by
  unfold a05413
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a05414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05412 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05413 ^ 1)
theorem ha05414 : a05414.IsHomogeneous 42 := by
  unfold a05414
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05413.pow 1)))

@[irreducible]
def a05415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05412 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05414 ^ 1)
theorem ha05415 : a05415.IsHomogeneous 42 := by
  unfold a05415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05414.pow 1)))

@[irreducible]
def a05416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a05415 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a02724 ^ 1)
theorem ha05416 : a05416.IsHomogeneous 48 := by
  unfold a05416
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha05415.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha02724.pow 1)))

@[irreducible]
def a05417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05416 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 3 * a05409 ^ 1)
theorem ha05417 : a05417.IsHomogeneous 48 := by
  unfold a05417
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05416.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 3)).mul (ha05409.pow 1)))

@[irreducible]
def a05418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05417 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a05410 ^ 1)
theorem ha05418 : a05418.IsHomogeneous 48 := by
  unfold a05418
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05417.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha05410.pow 1)))

@[irreducible]
def a05419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05411 ^ 1) + (C ((72 : ℂ) / (1 : ℂ)) * a05418 ^ 1)
theorem ha05419 : a05419.IsHomogeneous 48 := by
  unfold a05419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05411.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (1 : ℂ))).mul (ha05418.pow 1)))

@[irreducible]
def a05420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00133 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00317 ^ 1)
theorem ha05420 : a05420.IsHomogeneous 33 := by
  unfold a05420
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a05421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00324 ^ 1)
theorem ha05421 : a05421.IsHomogeneous 30 := by
  unfold a05421
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a05422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00324 ^ 1)
theorem ha05422 : a05422.IsHomogeneous 33 := by
  unfold a05422
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a05423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05422 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a05421 ^ 1)
theorem ha05423 : a05423.IsHomogeneous 33 := by
  unfold a05423
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05422.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha05421.pow 1)))

@[irreducible]
def a05424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00133 ^ 1)
theorem ha05424 : a05424.IsHomogeneous 27 := by
  unfold a05424
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a05425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00317 ^ 1)
theorem ha05425 : a05425.IsHomogeneous 33 := by
  unfold a05425
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a05426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05420 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a05424 ^ 1) + (C ((10 : ℂ) / (21 : ℂ)) * a05425 ^ 1)
theorem ha05426 : a05426.IsHomogeneous 33 := by
  unfold a05426
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05420.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha05424.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (21 : ℂ))).mul (ha05425.pow 1)))

@[irreducible]
def a05427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00133 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1)
theorem ha05427 : a05427.IsHomogeneous 30 := by
  unfold a05427
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a05428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05421 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a05427 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05424 ^ 1)
theorem ha05428 : a05428.IsHomogeneous 30 := by
  unfold a05428
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha05427.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05424.pow 1)))

@[irreducible]
def a05429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05426 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a05428 ^ 1)
theorem ha05429 : a05429.IsHomogeneous 33 := by
  unfold a05429
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05426.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha05428.pow 1)))

@[irreducible]
def a05430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00129 ^ 1)
theorem ha05430 : a05430.IsHomogeneous 33 := by
  unfold a05430
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a05431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00317 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha05431 : a05431.IsHomogeneous 33 := by
  unfold a05431
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a05432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05420 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a05430 ^ 1) + (C ((5 : ℂ) / (63 : ℂ)) * a05431 ^ 1)
theorem ha05432 : a05432.IsHomogeneous 33 := by
  unfold a05432
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha05430.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (63 : ℂ))).mul (ha05431.pow 1)))

@[irreducible]
def a05433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05422 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00644 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a05430 ^ 1)
theorem ha05433 : a05433.IsHomogeneous 33 := by
  unfold a05433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05422.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00644.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha05430.pow 1)))

@[irreducible]
def a05434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05432 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05433 ^ 1)
theorem ha05434 : a05434.IsHomogeneous 33 := by
  unfold a05434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05432.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05433.pow 1)))

@[irreducible]
def a05435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00032 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00865 ^ 1)
theorem ha05435 : a05435.IsHomogeneous 33 := by
  unfold a05435
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a05436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05425 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05431 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05435 ^ 1)
theorem ha05436 : a05436.IsHomogeneous 33 := by
  unfold a05436
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05431.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05435.pow 1)))

@[irreducible]
def a05437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05432 ^ 1) + (C ((10 : ℂ) / (21 : ℂ)) * a05436 ^ 1)
theorem ha05437 : a05437.IsHomogeneous 33 := by
  unfold a05437
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05432.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (21 : ℂ))).mul (ha05436.pow 1)))

@[irreducible]
def a05438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05434 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05437 ^ 1)
theorem ha05438 : a05438.IsHomogeneous 33 := by
  unfold a05438
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05429.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05434.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05437.pow 1)))

@[irreducible]
def a05439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a00649 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00133 ^ 1)
theorem ha05439 : a05439.IsHomogeneous 18 := by
  unfold a05439
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha00649.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a05440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a01607 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00324 ^ 1 * a00649 ^ 1)
theorem ha05440 : a05440.IsHomogeneous 18 := by
  unfold a05440
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha01607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)).mul (ha00649.pow 1)))

@[irreducible]
def a05441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05439 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a05440 ^ 1)
theorem ha05441 : a05441.IsHomogeneous 18 := by
  unfold a05441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05439.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha05440.pow 1)))

@[irreducible]
def a05442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05439 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00648 ^ 1)
theorem ha05442 : a05442.IsHomogeneous 18 := by
  unfold a05442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05439.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00648.pow 1)))

@[irreducible]
def a05443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05442 ^ 1)
theorem ha05443 : a05443.IsHomogeneous 18 := by
  unfold a05443
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05441.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05442.pow 1)))

@[irreducible]
def a05444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a03417 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00133 ^ 1 * a01607 ^ 1)
theorem ha05444 : a05444.IsHomogeneous 18 := by
  unfold a05444
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha03417.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00133.pow 1)).mul (ha01607.pow 1)))

@[irreducible]
def a05445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05440 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a05444 ^ 1)
theorem ha05445 : a05445.IsHomogeneous 18 := by
  unfold a05445
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha05444.pow 1)))

@[irreducible]
def a05446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05441 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a05445 ^ 1)
theorem ha05446 : a05446.IsHomogeneous 18 := by
  unfold a05446
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05441.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha05445.pow 1)))

@[irreducible]
def a05447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05443 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05446 ^ 1)
theorem ha05447 : a05447.IsHomogeneous 18 := by
  unfold a05447
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05443.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05446.pow 1)))

@[irreducible]
def a05448 : Poly := (C ((-7 : ℂ) / (20 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a05438 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05419 ^ 1) + (C ((49 : ℂ) / (116640 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00004 ^ 6 * a05447 ^ 1)
theorem ha05448 : a05448.IsHomogeneous 48 := by
  unfold a05448
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (20 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha05438.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05419.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((49 : ℂ) / (116640 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00004.pow 6)).mul (ha05447.pow 1)))

@[irreducible]
def a05449 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a05448 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02744 ^ 1)
theorem ha05449 : a05449.IsHomogeneous 93 := by
  unfold a05449
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05448.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02744.pow 1)))

@[irreducible]
def a05450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05404 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05449 ^ 1)
theorem ha05450 : a05450.IsHomogeneous 135 := by
  unfold a05450
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05404.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05449.pow 1)))

@[irreducible]
def a05451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05405 ^ 1)
theorem ha05451 : a05451.IsHomogeneous 141 := by
  unfold a05451
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05450.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05405.pow 1)))

@[irreducible]
def a05452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a03963 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a01938 ^ 1)
theorem ha05452 : a05452.IsHomogeneous 147 := by
  unfold a05452
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha03963.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a05453 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05403 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05452 ^ 1)
theorem ha05453 : a05453.IsHomogeneous 147 := by
  unfold a05453
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05403.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05452.pow 1)))

@[irreducible]
def a05454 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05405 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05453 ^ 1)
theorem ha05454 : a05454.IsHomogeneous 147 := by
  unfold a05454
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05405.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05453.pow 1)))

@[irreducible]
def a05455 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05454 ^ 1)
theorem ha05455 : a05455.IsHomogeneous 147 := by
  unfold a05455
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05454.pow 1)))

@[irreducible]
def a05456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01261 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00478 ^ 1 * a01841 ^ 1)
theorem ha05456 : a05456.IsHomogeneous 139 := by
  unfold a05456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00478.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a05457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01261 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a02810 ^ 1)
theorem ha05457 : a05457.IsHomogeneous 139 := by
  unfold a05457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01261.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha02810.pow 1)))

@[irreducible]
def a05458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05457 ^ 1)
theorem ha05458 : a05458.IsHomogeneous 139 := by
  unfold a05458
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05457.pow 1)))

@[irreducible]
def a05459 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00478 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00147 ^ 1 * a03803 ^ 1)
theorem ha05459 : a05459.IsHomogeneous 139 := by
  unfold a05459
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00478.pow 1)).mul (ha01841.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00147.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a05460 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a05459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05456 ^ 1)
theorem ha05460 : a05460.IsHomogeneous 139 := by
  unfold a05460
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha05459.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05456.pow 1)))

@[irreducible]
def a05461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05460 ^ 1)
theorem ha05461 : a05461.IsHomogeneous 139 := by
  unfold a05461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05460.pow 1)))

@[irreducible]
def a05462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a01228 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a01917 ^ 1)
theorem ha05462 : a05462.IsHomogeneous 123 := by
  unfold a05462
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha01228.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a05463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a01228 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a02754 ^ 1)
theorem ha05463 : a05463.IsHomogeneous 117 := by
  unfold a05463
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha01228.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a05464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05462 ^ 1)
theorem ha05464 : a05464.IsHomogeneous 123 := by
  unfold a05464
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05462.pow 1)))

@[irreducible]
def a05465 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a02754 ^ 1)
theorem ha05465 : a05465.IsHomogeneous 111 := by
  unfold a05465
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a05466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05463 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05465 ^ 1)
theorem ha05466 : a05466.IsHomogeneous 117 := by
  unfold a05466
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05463.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05465.pow 1)))

@[irreducible]
def a05467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05466 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05464 ^ 1)
theorem ha05467 : a05467.IsHomogeneous 123 := by
  unfold a05467
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05466.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05464.pow 1)))

@[irreducible]
def a05468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a03925 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a01917 ^ 1)
theorem ha05468 : a05468.IsHomogeneous 123 := by
  unfold a05468
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha03925.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a05469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05462 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05468 ^ 1)
theorem ha05469 : a05469.IsHomogeneous 123 := by
  unfold a05469
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05468.pow 1)))

@[irreducible]
def a05470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05469 ^ 1)
theorem ha05470 : a05470.IsHomogeneous 123 := by
  unfold a05470
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05469.pow 1)))

@[irreducible]
def a05471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05470 ^ 1)
theorem ha05471 : a05471.IsHomogeneous 123 := by
  unfold a05471
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05470.pow 1)))

@[irreducible]
def a05472 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00812 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00476 ^ 1 * a01903 ^ 1)
theorem ha05472 : a05472.IsHomogeneous 124 := by
  unfold a05472
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00812.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a05473 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00299 ^ 1 * a02806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01258 ^ 1)
theorem ha05473 : a05473.IsHomogeneous 124 := by
  unfold a05473
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00299.pow 1)).mul (ha02806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01258.pow 1)))

@[irreducible]
def a05474 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a05473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05472 ^ 1)
theorem ha05474 : a05474.IsHomogeneous 124 := by
  unfold a05474
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha05473.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05472.pow 1)))

@[irreducible]
def a05475 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00146 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a01903 ^ 1)
theorem ha05475 : a05475.IsHomogeneous 118 := by
  unfold a05475
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a05476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05475 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05472 ^ 1)
theorem ha05476 : a05476.IsHomogeneous 124 := by
  unfold a05476
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05475.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05472.pow 1)))

@[irreducible]
def a05477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05476 ^ 1)
theorem ha05477 : a05477.IsHomogeneous 124 := by
  unfold a05477
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05474.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05476.pow 1)))

@[irreducible]
def a05478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01240 ^ 1)
theorem ha05478 : a05478.IsHomogeneous 87 := by
  unfold a05478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a05479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02778 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01240 ^ 1)
theorem ha05479 : a05479.IsHomogeneous 87 := by
  unfold a05479
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02778.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a05480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05479 ^ 1)
theorem ha05480 : a05480.IsHomogeneous 87 := by
  unfold a05480
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05479.pow 1)))

@[irreducible]
def a05481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00139 ^ 1 * a03562 ^ 1)
theorem ha05481 : a05481.IsHomogeneous 87 := by
  unfold a05481
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00139.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a05482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05481 ^ 1)
theorem ha05482 : a05482.IsHomogeneous 87 := by
  unfold a05482
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05481.pow 1)))

@[irreducible]
def a05483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05482 ^ 1)
theorem ha05483 : a05483.IsHomogeneous 87 := by
  unfold a05483
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05482.pow 1)))

@[irreducible]
def a05484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a01207 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a00865 ^ 1)
theorem ha05484 : a05484.IsHomogeneous 39 := by
  unfold a05484
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a05485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a02710 ^ 1)
theorem ha05485 : a05485.IsHomogeneous 39 := by
  unfold a05485
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05484 ^ 1)
theorem ha05486 : a05486.IsHomogeneous 45 := by
  unfold a05486
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05485.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05484.pow 1)))

@[irreducible]
def a05487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00865 ^ 1)
theorem ha05487 : a05487.IsHomogeneous 33 := by
  unfold a05487
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a05488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05484 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a05487 ^ 1)
theorem ha05488 : a05488.IsHomogeneous 39 := by
  unfold a05488
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha05487.pow 1)))

@[irreducible]
def a05489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05486 ^ 1)
theorem ha05489 : a05489.IsHomogeneous 45 := by
  unfold a05489
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05486.pow 1)))

@[irreducible]
def a05490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05389 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02710 ^ 1)
theorem ha05490 : a05490.IsHomogeneous 42 := by
  unfold a05490
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05389.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05490 ^ 1) + (C ((135 : ℂ) / (28 : ℂ)) * a00003 ^ 3 * a05485 ^ 1)
theorem ha05491 : a05491.IsHomogeneous 42 := by
  unfold a05491
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05490.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (28 : ℂ))).mul (ha00003.pow 3)).mul (ha05485.pow 1)))

@[irreducible]
def a05492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05491 ^ 1) + (C ((135 : ℂ) / (28 : ℂ)) * a05486 ^ 1)
theorem ha05492 : a05492.IsHomogeneous 45 := by
  unfold a05492
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (28 : ℂ))).mul (ha05486.pow 1)))

@[irreducible]
def a05493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05489 ^ 1) + (C ((28 : ℂ) / (135 : ℂ)) * a05492 ^ 1)
theorem ha05493 : a05493.IsHomogeneous 45 := by
  unfold a05493
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05489.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (135 : ℂ))).mul (ha05492.pow 1)))

@[irreducible]
def a05494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00809 ^ 1)
theorem ha05494 : a05494.IsHomogeneous 33 := by
  unfold a05494
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a05495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00316 ^ 1 * a00809 ^ 1)
theorem ha05495 : a05495.IsHomogeneous 42 := by
  unfold a05495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a05496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05495 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05494 ^ 1)
theorem ha05496 : a05496.IsHomogeneous 42 := by
  unfold a05496
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05495.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05494.pow 1)))

@[irreducible]
def a05497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00864 ^ 1)
theorem ha05497 : a05497.IsHomogeneous 42 := by
  unfold a05497
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05495 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05497 ^ 1)
theorem ha05498 : a05498.IsHomogeneous 42 := by
  unfold a05498
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05495.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05497.pow 1)))

@[irreducible]
def a05499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05496 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05498 ^ 1)
theorem ha05499 : a05499.IsHomogeneous 42 := by
  unfold a05499
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05498.pow 1)))

@[irreducible]
def a05500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01896 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a03890 ^ 1)
theorem ha05500 : a05500.IsHomogeneous 33 := by
  unfold a05500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a05501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05494 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05500 ^ 1)
theorem ha05501 : a05501.IsHomogeneous 39 := by
  unfold a05501
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05494.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05500.pow 1)))

@[irreducible]
def a05502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05496 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05501 ^ 1)
theorem ha05502 : a05502.IsHomogeneous 45 := by
  unfold a05502
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05496.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05501.pow 1)))

@[irreducible]
def a05503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05502 ^ 1)
theorem ha05503 : a05503.IsHomogeneous 45 := by
  unfold a05503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05502.pow 1)))

@[irreducible]
def a05504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05493 ^ 1) + (C ((16 : ℂ) / (15 : ℂ)) * a05503 ^ 1)
theorem ha05504 : a05504.IsHomogeneous 45 := by
  unfold a05504
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (15 : ℂ))).mul (ha05503.pow 1)))

@[irreducible]
def a05505 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02778 ^ 1)
theorem ha05505 : a05505.IsHomogeneous 87 := by
  unfold a05505
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05504.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a05506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05505 ^ 1)
theorem ha05506 : a05506.IsHomogeneous 87 := by
  unfold a05506
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05505.pow 1)))

@[irreducible]
def a05507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05506 ^ 1)
theorem ha05507 : a05507.IsHomogeneous 87 := by
  unfold a05507
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05506.pow 1)))

@[irreducible]
def a05508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05507 ^ 1)
theorem ha05508 : a05508.IsHomogeneous 87 := by
  unfold a05508
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05507.pow 1)))

@[irreducible]
def a05509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a00817 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00300 ^ 1 * a01678 ^ 1)
theorem ha05509 : a05509.IsHomogeneous 107 := by
  unfold a05509
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00300.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a05510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00241 ^ 1 * a01914 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00817 ^ 1)
theorem ha05510 : a05510.IsHomogeneous 106 := by
  unfold a05510
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha01914.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a05511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05510 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a05509 ^ 1)
theorem ha05511 : a05511.IsHomogeneous 107 := by
  unfold a05511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha05509.pow 1)))

@[irreducible]
def a05512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00126 ^ 1 * a03534 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00300 ^ 1 * a01678 ^ 1)
theorem ha05512 : a05512.IsHomogeneous 107 := by
  unfold a05512
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00300.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a05513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05509 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a05512 ^ 1)
theorem ha05513 : a05513.IsHomogeneous 107 := by
  unfold a05513
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha05512.pow 1)))

@[irreducible]
def a05514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05511 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a05513 ^ 1)
theorem ha05514 : a05514.IsHomogeneous 107 := by
  unfold a05514
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05511.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha05513.pow 1)))

@[irreducible]
def a05515 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a03921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01914 ^ 1)
theorem ha05515 : a05515.IsHomogeneous 100 := by
  unfold a05515
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha03921.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a05516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05515 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05510 ^ 1)
theorem ha05516 : a05516.IsHomogeneous 106 := by
  unfold a05516
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05515.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05510.pow 1)))

@[irreducible]
def a05517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05511 ^ 1)
theorem ha05517 : a05517.IsHomogeneous 107 := by
  unfold a05517
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05511.pow 1)))

@[irreducible]
def a05518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05514 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05517 ^ 1)
theorem ha05518 : a05518.IsHomogeneous 107 := by
  unfold a05518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05517.pow 1)))

@[irreducible]
def a05519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05518 ^ 1) + (C ((9 : ℂ) / (20 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05508 ^ 1)
theorem ha05519 : a05519.IsHomogeneous 107 := by
  unfold a05519
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05518.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (20 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05508.pow 1)))

@[irreducible]
def a05520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01248 ^ 1)
theorem ha05520 : a05520.IsHomogeneous 87 := by
  unfold a05520
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a05521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02792 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01248 ^ 1)
theorem ha05521 : a05521.IsHomogeneous 87 := by
  unfold a05521
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a05522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05521 ^ 1)
theorem ha05522 : a05522.IsHomogeneous 87 := by
  unfold a05522
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05521.pow 1)))

@[irreducible]
def a05523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00141 ^ 1 * a03562 ^ 1)
theorem ha05523 : a05523.IsHomogeneous 87 := by
  unfold a05523
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00141.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a05524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05523 ^ 1)
theorem ha05524 : a05524.IsHomogeneous 87 := by
  unfold a05524
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05523.pow 1)))

@[irreducible]
def a05525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05524 ^ 1)
theorem ha05525 : a05525.IsHomogeneous 87 := by
  unfold a05525
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05524.pow 1)))

@[irreducible]
def a05526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05493 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a05503 ^ 1)
theorem ha05526 : a05526.IsHomogeneous 45 := by
  unfold a05526
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha05503.pow 1)))

@[irreducible]
def a05527 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02792 ^ 1)
theorem ha05527 : a05527.IsHomogeneous 87 := by
  unfold a05527
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05526.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a05528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05527 ^ 1)
theorem ha05528 : a05528.IsHomogeneous 87 := by
  unfold a05528
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05521.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05527.pow 1)))

@[irreducible]
def a05529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05528 ^ 1)
theorem ha05529 : a05529.IsHomogeneous 87 := by
  unfold a05529
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05528.pow 1)))

@[irreducible]
def a05530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05529 ^ 1)
theorem ha05530 : a05530.IsHomogeneous 87 := by
  unfold a05530
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05525.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05529.pow 1)))

@[irreducible]
def a05531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05518 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05530 ^ 1)
theorem ha05531 : a05531.IsHomogeneous 107 := by
  unfold a05531
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05518.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05530.pow 1)))

@[irreducible]
def a05532 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a05531 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05519 ^ 1)
theorem ha05532 : a05532.IsHomogeneous 107 := by
  unfold a05532
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha05531.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05519.pow 1)))

@[irreducible]
def a05533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01253 ^ 1)
theorem ha05533 : a05533.IsHomogeneous 87 := by
  unfold a05533
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a05534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02799 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01253 ^ 1)
theorem ha05534 : a05534.IsHomogeneous 87 := by
  unfold a05534
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02799.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a05535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05534 ^ 1)
theorem ha05535 : a05535.IsHomogeneous 87 := by
  unfold a05535
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05533.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05534.pow 1)))

@[irreducible]
def a05536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05493 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a05503 ^ 1)
theorem ha05536 : a05536.IsHomogeneous 45 := by
  unfold a05536
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha05503.pow 1)))

@[irreducible]
def a05537 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02799 ^ 1)
theorem ha05537 : a05537.IsHomogeneous 87 := by
  unfold a05537
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05536.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a05538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05537 ^ 1)
theorem ha05538 : a05538.IsHomogeneous 87 := by
  unfold a05538
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05537.pow 1)))

@[irreducible]
def a05539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05538 ^ 1)
theorem ha05539 : a05539.IsHomogeneous 87 := by
  unfold a05539
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05538.pow 1)))

@[irreducible]
def a05540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00144 ^ 1 * a03562 ^ 1)
theorem ha05540 : a05540.IsHomogeneous 87 := by
  unfold a05540
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00144.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a05541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05540 ^ 1)
theorem ha05541 : a05541.IsHomogeneous 87 := by
  unfold a05541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05533.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05540.pow 1)))

@[irreducible]
def a05542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05541 ^ 1)
theorem ha05542 : a05542.IsHomogeneous 87 := by
  unfold a05542
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05541.pow 1)))

@[irreducible]
def a05543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05539 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05542 ^ 1)
theorem ha05543 : a05543.IsHomogeneous 87 := by
  unfold a05543
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05542.pow 1)))

@[irreducible]
def a05544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05518 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05543 ^ 1)
theorem ha05544 : a05544.IsHomogeneous 107 := by
  unfold a05544
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05518.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05543.pow 1)))

@[irreducible]
def a05545 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a05544 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05532 ^ 1)
theorem ha05545 : a05545.IsHomogeneous 107 := by
  unfold a05545
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha05544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05532.pow 1)))

@[irreducible]
def a05546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a02806 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00127 ^ 1 * a05545 ^ 1)
theorem ha05546 : a05546.IsHomogeneous 125 := by
  unfold a05546
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha02806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00127.pow 1)).mul (ha05545.pow 1)))

@[irreducible]
def a05547 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a05546 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05473 ^ 1)
theorem ha05547 : a05547.IsHomogeneous 125 := by
  unfold a05547
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha05546.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05473.pow 1)))

@[irreducible]
def a05548 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a05547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05474 ^ 1)
theorem ha05548 : a05548.IsHomogeneous 125 := by
  unfold a05548
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha05547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05474.pow 1)))

@[irreducible]
def a05549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05477 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05548 ^ 1)
theorem ha05549 : a05549.IsHomogeneous 125 := by
  unfold a05549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05477.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05548.pow 1)))

@[irreducible]
def a05550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05549 ^ 1) + (C ((27 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a05471 ^ 1)
theorem ha05550 : a05550.IsHomogeneous 131 := by
  unfold a05550
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05549.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05471.pow 1)))

@[irreducible]
def a05551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02810 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a05550 ^ 1)
theorem ha05551 : a05551.IsHomogeneous 137 := by
  unfold a05551
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02810.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha05550.pow 1)))

@[irreducible]
def a05552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a05457 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a05551 ^ 1)
theorem ha05552 : a05552.IsHomogeneous 143 := by
  unfold a05552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha05457.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha05551.pow 1)))

@[irreducible]
def a05553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a05458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05552 ^ 1)
theorem ha05553 : a05553.IsHomogeneous 143 := by
  unfold a05553
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha05458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05552.pow 1)))

@[irreducible]
def a05554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a05461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05553 ^ 1)
theorem ha05554 : a05554.IsHomogeneous 143 := by
  unfold a05554
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha05461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05553.pow 1)))

@[irreducible]
def a05555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a05554 ^ 1) + (C ((81 : ℂ) / (1000 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a05455 ^ 1)
theorem ha05555 : a05555.IsHomogeneous 155 := by
  unfold a05555
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha05554.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (1000 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05455.pow 1)))

@[irreducible]
def a05556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a05555 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a02814 ^ 1)
theorem ha05556 : a05556.IsHomogeneous 185 := by
  unfold a05556
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha05555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a05557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05556 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05398 ^ 1)
theorem ha05557 : a05557.IsHomogeneous 185 := by
  unfold a05557
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05556.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05398.pow 1)))

@[irreducible]
def a05558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05557 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05399 ^ 1)
theorem ha05558 : a05558.IsHomogeneous 185 := by
  unfold a05558
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05557.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05399.pow 1)))

@[irreducible]
def a05559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05558 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05402 ^ 1)
theorem ha05559 : a05559.IsHomogeneous 185 := by
  unfold a05559
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05402.pow 1)))

@[irreducible]
def a05560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05559 ^ 1) + (C ((27 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a05396 ^ 1)
theorem ha05560 : a05560.IsHomogeneous 185 := by
  unfold a05560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05559.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha05396.pow 1)))

@[irreducible]
def a05561 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00836 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a01949 ^ 1)
theorem ha05561 : a05561.IsHomogeneous 385 := by
  unfold a05561
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00836.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a05562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02851 ^ 1)
theorem ha05562 : a05562.IsHomogeneous 361 := by
  unfold a05562
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha01284.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a05563 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a05562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05561 ^ 1)
theorem ha05563 : a05563.IsHomogeneous 385 := by
  unfold a05563
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha05562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05561.pow 1)))

@[irreducible]
def a05564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00316 ^ 1 * a00831 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a01941 ^ 1)
theorem ha05564 : a05564.IsHomogeneous 126 := by
  unfold a05564
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00316.pow 1)).mul (ha00831.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha01941.pow 1)))

@[irreducible]
def a05565 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00831 ^ 1)
theorem ha05565 : a05565.IsHomogeneous 90 := by
  unfold a05565
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a05566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05564 ^ 1)
theorem ha05566 : a05566.IsHomogeneous 126 := by
  unfold a05566
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05564.pow 1)))

@[irreducible]
def a05567 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00864 ^ 1)
theorem ha05567 : a05567.IsHomogeneous 54 := by
  unfold a05567
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05568 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05567 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05565 ^ 1)
theorem ha05568 : a05568.IsHomogeneous 90 := by
  unfold a05568
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05567.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05565.pow 1)))

@[irreducible]
def a05569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05568 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05566 ^ 1)
theorem ha05569 : a05569.IsHomogeneous 126 := by
  unfold a05569
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05566.pow 1)))

@[irreducible]
def a05570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03967 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01941 ^ 1)
theorem ha05570 : a05570.IsHomogeneous 129 := by
  unfold a05570
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03967.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01941.pow 1)))

@[irreducible]
def a05571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05564 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05570 ^ 1)
theorem ha05571 : a05571.IsHomogeneous 129 := by
  unfold a05571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05564.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05570.pow 1)))

@[irreducible]
def a05572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05571 ^ 1)
theorem ha05572 : a05572.IsHomogeneous 129 := by
  unfold a05572
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05566.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05571.pow 1)))

@[irreducible]
def a05573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05572 ^ 1)
theorem ha05573 : a05573.IsHomogeneous 129 := by
  unfold a05573
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05572.pow 1)))

@[irreducible]
def a05574 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00487 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01281 ^ 1)
theorem ha05574 : a05574.IsHomogeneous 148 := by
  unfold a05574
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00487.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a05575 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02847 ^ 1)
theorem ha05575 : a05575.IsHomogeneous 154 := by
  unfold a05575
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01281.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02847.pow 1)))

@[irreducible]
def a05576 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05575 ^ 1)
theorem ha05576 : a05576.IsHomogeneous 154 := by
  unfold a05576
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05575.pow 1)))

@[irreducible]
def a05577 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00487 ^ 1 * a00865 ^ 1)
theorem ha05577 : a05577.IsHomogeneous 106 := by
  unfold a05577
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a05578 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05577 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05574 ^ 1)
theorem ha05578 : a05578.IsHomogeneous 148 := by
  unfold a05578
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05577.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05574.pow 1)))

@[irreducible]
def a05579 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05578 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05576 ^ 1)
theorem ha05579 : a05579.IsHomogeneous 154 := by
  unfold a05579
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05578.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05576.pow 1)))

@[irreducible]
def a05580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a01275 ^ 1)
theorem ha05580 : a05580.IsHomogeneous 136 := by
  unfold a05580
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05581 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a01275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02837 ^ 1)
theorem ha05581 : a05581.IsHomogeneous 137 := by
  unfold a05581
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha01275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02837.pow 1)))

@[irreducible]
def a05582 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05581 ^ 1)
theorem ha05582 : a05582.IsHomogeneous 137 := by
  unfold a05582
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05581.pow 1)))

@[irreducible]
def a05583 : Poly := (C ((-4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01702 ^ 1)
theorem ha05583 : a05583.IsHomogeneous 136 := by
  unfold a05583
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a05584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05583 ^ 1)
theorem ha05584 : a05584.IsHomogeneous 136 := by
  unfold a05584
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05583.pow 1)))

@[irreducible]
def a05585 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05584 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05582 ^ 1)
theorem ha05585 : a05585.IsHomogeneous 137 := by
  unfold a05585
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05582.pow 1)))

@[irreducible]
def a05586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00691 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a01678 ^ 1)
theorem ha05586 : a05586.IsHomogeneous 101 := by
  unfold a05586
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00691.pow 1)).mul (ha00712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a05587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01702 ^ 1)
theorem ha05587 : a05587.IsHomogeneous 100 := by
  unfold a05587
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a05588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05586 ^ 1)
theorem ha05588 : a05588.IsHomogeneous 101 := by
  unfold a05588
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05586.pow 1)))

@[irreducible]
def a05589 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a03534 ^ 1)
theorem ha05589 : a05589.IsHomogeneous 95 := by
  unfold a05589
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha01678.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a05590 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05586 ^ 1)
theorem ha05590 : a05590.IsHomogeneous 101 := by
  unfold a05590
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05586.pow 1)))

@[irreducible]
def a05591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05590 ^ 1)
theorem ha05591 : a05591.IsHomogeneous 101 := by
  unfold a05591
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05588.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05590.pow 1)))

@[irreducible]
def a05592 : Poly := (C ((-4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01702 ^ 1)
theorem ha05592 : a05592.IsHomogeneous 100 := by
  unfold a05592
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a05593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05592 ^ 1)
theorem ha05593 : a05593.IsHomogeneous 100 := by
  unfold a05593
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05592.pow 1)))

@[irreducible]
def a05594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05593 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05588 ^ 1)
theorem ha05594 : a05594.IsHomogeneous 101 := by
  unfold a05594
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05593.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05588.pow 1)))

@[irreducible]
def a05595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05594 ^ 1)
theorem ha05595 : a05595.IsHomogeneous 101 := by
  unfold a05595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05591.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05594.pow 1)))

@[irreducible]
def a05596 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05595 ^ 1)
theorem ha05596 : a05596.IsHomogeneous 137 := by
  unfold a05596
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a05597 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a05596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05581 ^ 1)
theorem ha05597 : a05597.IsHomogeneous 137 := by
  unfold a05597
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha05596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05581.pow 1)))

@[irreducible]
def a05598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05582 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05597 ^ 1)
theorem ha05598 : a05598.IsHomogeneous 137 := by
  unfold a05598
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05597.pow 1)))

@[irreducible]
def a05599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05585 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05598 ^ 1)
theorem ha05599 : a05599.IsHomogeneous 137 := by
  unfold a05599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05585.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05598.pow 1)))

@[irreducible]
def a05600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a00829 ^ 1)
theorem ha05600 : a05600.IsHomogeneous 137 := by
  unfold a05600
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a05601 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00241 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a00829 ^ 1)
theorem ha05601 : a05601.IsHomogeneous 137 := by
  unfold a05601
  exact (((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00241.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a05602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05601 ^ 1)
theorem ha05602 : a05602.IsHomogeneous 137 := by
  unfold a05602
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05601.pow 1)))

@[irreducible]
def a05603 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a03534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01678 ^ 1)
theorem ha05603 : a05603.IsHomogeneous 95 := by
  unfold a05603
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a05604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05603 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05600 ^ 1)
theorem ha05604 : a05604.IsHomogeneous 137 := by
  unfold a05604
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05603.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05600.pow 1)))

@[irreducible]
def a05605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05604 ^ 1)
theorem ha05605 : a05605.IsHomogeneous 137 := by
  unfold a05605
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05604.pow 1)))

@[irreducible]
def a05606 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a03963 ^ 1)
theorem ha05606 : a05606.IsHomogeneous 136 := by
  unfold a05606
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a05607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05601 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05606 ^ 1)
theorem ha05607 : a05607.IsHomogeneous 137 := by
  unfold a05607
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05601.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05606.pow 1)))

@[irreducible]
def a05608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05607 ^ 1)
theorem ha05608 : a05608.IsHomogeneous 137 := by
  unfold a05608
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05607.pow 1)))

@[irreducible]
def a05609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05608 ^ 1)
theorem ha05609 : a05609.IsHomogeneous 137 := by
  unfold a05609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05608.pow 1)))

@[irreducible]
def a05610 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a05609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05599 ^ 1)
theorem ha05610 : a05610.IsHomogeneous 137 := by
  unfold a05610
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha05609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05599.pow 1)))

@[irreducible]
def a05611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05610 ^ 1)
theorem ha05611 : a05611.IsHomogeneous 161 := by
  unfold a05611
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha02847.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05610.pow 1)))

@[irreducible]
def a05612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05611 ^ 1)
theorem ha05612 : a05612.IsHomogeneous 161 := by
  unfold a05612
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05611.pow 1)))

@[irreducible]
def a05613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05612 ^ 1)
theorem ha05613 : a05613.IsHomogeneous 161 := by
  unfold a05613
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05612.pow 1)))

@[irreducible]
def a05614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05613 ^ 1)
theorem ha05614 : a05614.IsHomogeneous 161 := by
  unfold a05614
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05579.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05613.pow 1)))

@[irreducible]
def a05615 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a05573 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05614 ^ 1)
theorem ha05615 : a05615.IsHomogeneous 161 := by
  unfold a05615
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha05573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05614.pow 1)))

@[irreducible]
def a05616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a02851 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05615 ^ 1)
theorem ha05616 : a05616.IsHomogeneous 271 := by
  unfold a05616
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha02851.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05615.pow 1)))

@[irreducible]
def a05617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05562 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a05616 ^ 1)
theorem ha05617 : a05617.IsHomogeneous 361 := by
  unfold a05617
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05562.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05616.pow 1)))

@[irreducible]
def a05618 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a05617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05563 ^ 1)
theorem ha05618 : a05618.IsHomogeneous 385 := by
  unfold a05618
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha05617.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05563.pow 1)))

@[irreducible]
def a05619 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a03978 ^ 1)
theorem ha05619 : a05619.IsHomogeneous 409 := by
  unfold a05619
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha01949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a05620 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05619 ^ 1)
theorem ha05620 : a05620.IsHomogeneous 409 := by
  unfold a05620
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05561.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05619.pow 1)))

@[irreducible]
def a05621 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05620 ^ 1)
theorem ha05621 : a05621.IsHomogeneous 409 := by
  unfold a05621
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05563.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05620.pow 1)))

@[irreducible]
def a05622 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05621 ^ 1)
theorem ha05622 : a05622.IsHomogeneous 409 := by
  unfold a05622
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05621.pow 1)))

@[irreducible]
def a05623 : Poly := (C ((-25 : ℂ) / (6561 : ℂ)) * a00003 ^ 2 * a00042 ^ 4 * a00100 ^ 4 * a05560 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a05622 ^ 1)
theorem ha05623 : a05623.IsHomogeneous 427 := by
  unfold a05623
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (6561 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha05560.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha05622.pow 1)))

@[irreducible]
def a05624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02857 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05623 ^ 1)
theorem ha05624 : a05624.IsHomogeneous 427 := by
  unfold a05624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02857.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05623.pow 1)))

@[irreducible]
def a05625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05624 ^ 1)
theorem ha05625 : a05625.IsHomogeneous 427 := by
  unfold a05625
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05375.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05624.pow 1)))

@[irreducible]
def a05626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05376 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05625 ^ 1)
theorem ha05626 : a05626.IsHomogeneous 427 := by
  unfold a05626
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05625.pow 1)))

@[irreducible]
def a05627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05626 ^ 1)
theorem ha05627 : a05627.IsHomogeneous 427 := by
  unfold a05627
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05626.pow 1)))

@[irreducible]
def a05628 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a02860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a05627 ^ 1)
theorem ha05628 : a05628.IsHomogeneous 853 := by
  unfold a05628
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha02860.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha05627.pow 1)))

@[irreducible]
def a05629 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05369 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05628 ^ 1)
theorem ha05629 : a05629.IsHomogeneous 1186 := by
  unfold a05629
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05369.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05628.pow 1)))

@[irreducible]
def a05630 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05629 ^ 1)
theorem ha05630 : a05630.IsHomogeneous 1519 := by
  unfold a05630
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05370.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05629.pow 1)))

@[irreducible]
def a05631 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a05373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05630 ^ 1)
theorem ha05631 : a05631.IsHomogeneous 1852 := by
  unfold a05631
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha05373.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05630.pow 1)))

end CycleQ2Concrete
