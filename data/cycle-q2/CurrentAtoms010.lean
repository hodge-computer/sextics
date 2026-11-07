import Proposal.CurrentAtoms009

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a04352 : Poly := (C ((-200 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a04351 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04350 ^ 1)
theorem ha04352 : a04352.IsHomogeneous 165 := by
  unfold a04352
  exact (((((isHomogeneous_C (σ := Fin 6) ((-200 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha04351.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04350.pow 1)))

@[irreducible]
def a04353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha04353 : a04353.IsHomogeneous 6 := by
  unfold a04353
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a04354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01045 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04353 ^ 1)
theorem ha04354 : a04354.IsHomogeneous 34 := by
  unfold a04354
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01045.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04353.pow 1)))

@[irreducible]
def a04355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04354 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04353 ^ 1)
theorem ha04355 : a04355.IsHomogeneous 34 := by
  unfold a04355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04354.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04353.pow 1)))

@[irreducible]
def a04356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a04355 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a02126 ^ 1)
theorem ha04356 : a04356.IsHomogeneous 40 := by
  unfold a04356
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha04355.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha02126.pow 1)))

@[irreducible]
def a04357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha04357 : a04357.IsHomogeneous 12 := by
  unfold a04357
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a04358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a04357 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01047 ^ 1)
theorem ha04358 : a04358.IsHomogeneous 31 := by
  unfold a04358
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04357.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01047.pow 1)))

@[irreducible]
def a04359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04358 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01047 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a04357 ^ 1)
theorem ha04359 : a04359.IsHomogeneous 31 := by
  unfold a04359
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04358.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01047.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04357.pow 1)))

@[irreducible]
def a04360 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a04359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04356 ^ 1)
theorem ha04360 : a04360.IsHomogeneous 40 := by
  unfold a04360
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04356.pow 1)))

@[irreducible]
def a04361 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02129 ^ 1)
theorem ha04361 : a04361.IsHomogeneous 78 := by
  unfold a04361
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04360.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02129.pow 1)))

@[irreducible]
def a04362 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00100 ^ 1 * a02236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a00950 ^ 1)
theorem ha04362 : a04362.IsHomogeneous 122 := by
  unfold a04362
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha02236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha00950.pow 1)))

@[irreducible]
def a04363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04362 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04361 ^ 1)
theorem ha04363 : a04363.IsHomogeneous 127 := by
  unfold a04363
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04362.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04361.pow 1)))

@[irreducible]
def a04364 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00393 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a01092 ^ 1)
theorem ha04364 : a04364.IsHomogeneous 127 := by
  unfold a04364
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00393.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a04365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04363 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a04364 ^ 1)
theorem ha04365 : a04365.IsHomogeneous 127 := by
  unfold a04365
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha04364.pow 1)))

@[irreducible]
def a04366 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a02295 ^ 1)
theorem ha04366 : a04366.IsHomogeneous 147 := by
  unfold a04366
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha00982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a04367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04366 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 2 * a04365 ^ 1)
theorem ha04367 : a04367.IsHomogeneous 147 := by
  unfold a04367
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04366.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04365.pow 1)))

@[irreducible]
def a04368 : Poly := (C ((-1 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00009 ^ 1)
theorem ha04368 : a04368.IsHomogeneous 15 := by
  unfold a04368
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a04369 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a02133 ^ 1)
theorem ha04369 : a04369.IsHomogeneous 115 := by
  unfold a04369
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a04370 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00146 ^ 1 * a02242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a00953 ^ 1)
theorem ha04370 : a04370.IsHomogeneous 127 := by
  unfold a04370
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha00953.pow 1)))

@[irreducible]
def a04371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04370 ^ 1) + (C ((3 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a04369 ^ 1)
theorem ha04371 : a04371.IsHomogeneous 127 := by
  unfold a04371
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04370.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha04369.pow 1)))

@[irreducible]
def a04372 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00387 ^ 1 * a01052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a01079 ^ 1)
theorem ha04372 : a04372.IsHomogeneous 121 := by
  unfold a04372
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a04373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04371 ^ 1)
theorem ha04373 : a04373.IsHomogeneous 127 := by
  unfold a04373
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04372.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04371.pow 1)))

@[irreducible]
def a04374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a02278 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a00974 ^ 1)
theorem ha04374 : a04374.IsHomogeneous 115 := by
  unfold a04374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha02278.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha00974.pow 1)))

@[irreducible]
def a04375 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04374 ^ 1)
theorem ha04375 : a04375.IsHomogeneous 129 := by
  unfold a04375
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04373.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04374.pow 1)))

@[irreducible]
def a04376 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00368 ^ 1)
theorem ha04376 : a04376.IsHomogeneous 12 := by
  unfold a04376
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a04377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a01057 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a04376 ^ 1)
theorem ha04377 : a04377.IsHomogeneous 31 := by
  unfold a04377
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01057.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04376.pow 1)))

@[irreducible]
def a04378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04377 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a01057 ^ 1)
theorem ha04378 : a04378.IsHomogeneous 31 := by
  unfold a04378
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04377.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01057.pow 1)))

@[irreducible]
def a04379 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04378 ^ 1)
theorem ha04379 : a04379.IsHomogeneous 67 := by
  unfold a04379
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04378.pow 1)))

@[irreducible]
def a04380 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02252 ^ 1)
theorem ha04380 : a04380.IsHomogeneous 85 := by
  unfold a04380
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00958.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a04381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04380 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04379 ^ 1)
theorem ha04381 : a04381.IsHomogeneous 85 := by
  unfold a04381
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04380.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04379.pow 1)))

@[irreducible]
def a04382 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01060 ^ 1)
theorem ha04382 : a04382.IsHomogeneous 85 := by
  unfold a04382
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a04383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04381 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a04382 ^ 1)
theorem ha04383 : a04383.IsHomogeneous 85 := by
  unfold a04383
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha04382.pow 1)))

@[irreducible]
def a04384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00465 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00139 ^ 1 * a00188 ^ 1)
theorem ha04384 : a04384.IsHomogeneous 73 := by
  unfold a04384
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00465.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00139.pow 1)).mul (ha00188.pow 1)))

@[irreducible]
def a04385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04384 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04383 ^ 1)
theorem ha04385 : a04385.IsHomogeneous 87 := by
  unfold a04385
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04384.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04383.pow 1)))

@[irreducible]
def a04386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00173 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00039 ^ 1 * a00300 ^ 1)
theorem ha04386 : a04386.IsHomogeneous 85 := by
  unfold a04386
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00173.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00039.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a04387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04385 ^ 1) + (C ((32 : ℂ) / (27 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a04386 ^ 1)
theorem ha04387 : a04387.IsHomogeneous 87 := by
  unfold a04387
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04385.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (27 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha04386.pow 1)))

@[irreducible]
def a04388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1)
theorem ha04388 : a04388.IsHomogeneous 30 := by
  unfold a04388
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a04389 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a04388 ^ 1)
theorem ha04389 : a04389.IsHomogeneous 37 := by
  unfold a04389
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01057.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha04388.pow 1)))

@[irreducible]
def a04390 : Poly := (C ((-1 : ℂ) / (864 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a04376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04389 ^ 1)
theorem ha04390 : a04390.IsHomogeneous 37 := by
  unfold a04390
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha04376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04389.pow 1)))

@[irreducible]
def a04391 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a02144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04390 ^ 1)
theorem ha04391 : a04391.IsHomogeneous 73 := by
  unfold a04391
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha02144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04390.pow 1)))

@[irreducible]
def a04392 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02261 ^ 1)
theorem ha04392 : a04392.IsHomogeneous 85 := by
  unfold a04392
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02261.pow 1)))

@[irreducible]
def a04393 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04391 ^ 1)
theorem ha04393 : a04393.IsHomogeneous 87 := by
  unfold a04393
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04392.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04391.pow 1)))

@[irreducible]
def a04394 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01067 ^ 1)
theorem ha04394 : a04394.IsHomogeneous 85 := by
  unfold a04394
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00379.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a04395 : Poly := (C ((-15 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04394 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04393 ^ 1)
theorem ha04395 : a04395.IsHomogeneous 87 := by
  unfold a04395
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04394.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04393.pow 1)))

@[irreducible]
def a04396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00469 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00141 ^ 1 * a00188 ^ 1)
theorem ha04396 : a04396.IsHomogeneous 73 := by
  unfold a04396
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00141.pow 1)).mul (ha00188.pow 1)))

@[irreducible]
def a04397 : Poly := (C ((-30 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04396 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04395 ^ 1)
theorem ha04397 : a04397.IsHomogeneous 87 := by
  unfold a04397
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-30 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04396.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04395.pow 1)))

@[irreducible]
def a04398 : Poly := (C ((-80 : ℂ) / (3 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a04386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04397 ^ 1)
theorem ha04398 : a04398.IsHomogeneous 87 := by
  unfold a04398
  exact (((((isHomogeneous_C (σ := Fin 6) ((-80 : ℂ) / (3 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha04386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04397.pow 1)))

@[irreducible]
def a04399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04387 ^ 1) + (C ((1 : ℂ) / (75 : ℂ)) * a04398 ^ 1)
theorem ha04399 : a04399.IsHomogeneous 87 := by
  unfold a04399
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (75 : ℂ))).mul (ha04398.pow 1)))

@[irreducible]
def a04400 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a04388 ^ 1)
theorem ha04400 : a04400.IsHomogeneous 37 := by
  unfold a04400
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01057.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha04388.pow 1)))

@[irreducible]
def a04401 : Poly := (C ((-1 : ℂ) / (288 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a04376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04400 ^ 1)
theorem ha04401 : a04401.IsHomogeneous 37 := by
  unfold a04401
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha04376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04400.pow 1)))

@[irreducible]
def a04402 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04401 ^ 1)
theorem ha04402 : a04402.IsHomogeneous 37 := by
  unfold a04402
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04401.pow 1)))

@[irreducible]
def a04403 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a02152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04402 ^ 1)
theorem ha04403 : a04403.IsHomogeneous 73 := by
  unfold a04403
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha02152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04402.pow 1)))

@[irreducible]
def a04404 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02271 ^ 1)
theorem ha04404 : a04404.IsHomogeneous 85 := by
  unfold a04404
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02271.pow 1)))

@[irreducible]
def a04405 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04403 ^ 1)
theorem ha04405 : a04405.IsHomogeneous 87 := by
  unfold a04405
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04404.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04403.pow 1)))

@[irreducible]
def a04406 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01074 ^ 1)
theorem ha04406 : a04406.IsHomogeneous 85 := by
  unfold a04406
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00384.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a04407 : Poly := (C ((-27 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04406 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04405 ^ 1)
theorem ha04407 : a04407.IsHomogeneous 87 := by
  unfold a04407
  exact (((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04405.pow 1)))

@[irreducible]
def a04408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00473 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00144 ^ 1 * a00188 ^ 1)
theorem ha04408 : a04408.IsHomogeneous 73 := by
  unfold a04408
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00144.pow 1)).mul (ha00188.pow 1)))

@[irreducible]
def a04409 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04408 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04407 ^ 1)
theorem ha04409 : a04409.IsHomogeneous 87 := by
  unfold a04409
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04408.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04407.pow 1)))

@[irreducible]
def a04410 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a04386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04409 ^ 1)
theorem ha04410 : a04410.IsHomogeneous 87 := by
  unfold a04410
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha04386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04409.pow 1)))

@[irreducible]
def a04411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04399 ^ 1) + (C ((1 : ℂ) / (45 : ℂ)) * a04410 ^ 1)
theorem ha04411 : a04411.IsHomogeneous 87 := by
  unfold a04411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04399.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (45 : ℂ))).mul (ha04410.pow 1)))

@[irreducible]
def a04412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a04411 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a02157 ^ 1)
theorem ha04412 : a04412.IsHomogeneous 105 := by
  unfold a04412
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha04411.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha02157.pow 1)))

@[irreducible]
def a04413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a04412 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a04375 ^ 1)
theorem ha04413 : a04413.IsHomogeneous 129 := by
  unfold a04413
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha04412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha04375.pow 1)))

@[irreducible]
def a04414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04413 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02158 ^ 1)
theorem ha04414 : a04414.IsHomogeneous 129 := by
  unfold a04414
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02158.pow 1)))

@[irreducible]
def a04415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04367 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a00014 ^ 3 * a04414 ^ 1)
theorem ha04415 : a04415.IsHomogeneous 147 := by
  unfold a04415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04367.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha00014.pow 3)).mul (ha04414.pow 1)))

@[irreducible]
def a04416 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a02159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04415 ^ 1)
theorem ha04416 : a04416.IsHomogeneous 177 := by
  unfold a04416
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha02159.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04415.pow 1)))

@[irreducible]
def a04417 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00014 ^ 2 * a04352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04416 ^ 1)
theorem ha04417 : a04417.IsHomogeneous 177 := by
  unfold a04417
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00014.pow 2)).mul (ha04352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04416.pow 1)))

@[irreducible]
def a04418 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a02308 ^ 1)
theorem ha04418 : a04418.IsHomogeneous 437 := by
  unfold a04418
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha00988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a04419 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00398 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a01103 ^ 1)
theorem ha04419 : a04419.IsHomogeneous 416 := by
  unfold a04419
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00398.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04420 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a00986 ^ 1)
theorem ha04420 : a04420.IsHomogeneous 389 := by
  unfold a04420
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha00986.pow 1)))

@[irreducible]
def a04421 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00155 ^ 1 * a00395 ^ 1)
theorem ha04421 : a04421.IsHomogeneous 133 := by
  unfold a04421
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha01097.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00155.pow 1)).mul (ha00395.pow 1)))

@[irreducible]
def a04422 : Poly := (C ((-5 : ℂ) / (1296 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a04421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a01088 ^ 1)
theorem ha04422 : a04422.IsHomogeneous 140 := by
  unfold a04422
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha04421.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha01088.pow 1)))

@[irreducible]
def a04423 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02302 ^ 1)
theorem ha04423 : a04423.IsHomogeneous 142 := by
  unfold a04423
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02302.pow 1)))

@[irreducible]
def a04424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04423 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04422 ^ 1)
theorem ha04424 : a04424.IsHomogeneous 142 := by
  unfold a04424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04423.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04422.pow 1)))

@[irreducible]
def a04425 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00260 ^ 1)
theorem ha04425 : a04425.IsHomogeneous 67 := by
  unfold a04425
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04426 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00241 ^ 1)
theorem ha04426 : a04426.IsHomogeneous 86 := by
  unfold a04426
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a04427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04426 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a04425 ^ 1)
theorem ha04427 : a04427.IsHomogeneous 86 := by
  unfold a04427
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04426.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha04425.pow 1)))

@[irreducible]
def a04428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a04427 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00061 ^ 1 * a00211 ^ 1)
theorem ha04428 : a04428.IsHomogeneous 91 := by
  unfold a04428
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha04427.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00061.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a04429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a04426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04428 ^ 1)
theorem ha04429 : a04429.IsHomogeneous 91 := by
  unfold a04429
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha04426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04428.pow 1)))

@[irreducible]
def a04430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a04425 ^ 1)
theorem ha04430 : a04430.IsHomogeneous 91 := by
  unfold a04430
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04429.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04425.pow 1)))

@[irreducible]
def a04431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02166 ^ 1)
theorem ha04431 : a04431.IsHomogeneous 127 := by
  unfold a04431
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04430.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a04432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00982 ^ 1)
theorem ha04432 : a04432.IsHomogeneous 136 := by
  unfold a04432
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a04433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a04432 ^ 1)
theorem ha04433 : a04433.IsHomogeneous 140 := by
  unfold a04433
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04431.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha04432.pow 1)))

@[irreducible]
def a04434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00211 ^ 1 * a00393 ^ 1)
theorem ha04434 : a04434.IsHomogeneous 139 := by
  unfold a04434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00211.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a04435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04433 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a04434 ^ 1)
theorem ha04435 : a04435.IsHomogeneous 140 := by
  unfold a04435
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04433.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha04434.pow 1)))

@[irreducible]
def a04436 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00484 ^ 1)
theorem ha04436 : a04436.IsHomogeneous 122 := by
  unfold a04436
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a04437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04435 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 2 * a04436 ^ 1)
theorem ha04437 : a04437.IsHomogeneous 140 := by
  unfold a04437
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04435.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04436.pow 1)))

@[irreducible]
def a04438 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00260 ^ 1)
theorem ha04438 : a04438.IsHomogeneous 67 := by
  unfold a04438
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04437 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 1 * a04438 ^ 1)
theorem ha04439 : a04439.IsHomogeneous 140 := by
  unfold a04439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04437.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha04438.pow 1)))

@[irreducible]
def a04440 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a02170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a04439 ^ 1)
theorem ha04440 : a04440.IsHomogeneous 164 := by
  unfold a04440
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha02170.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha04439.pow 1)))

@[irreducible]
def a04441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04440 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a04424 ^ 1)
theorem ha04441 : a04441.IsHomogeneous 164 := by
  unfold a04441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04440.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04424.pow 1)))

@[irreducible]
def a04442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a02171 ^ 1)
theorem ha04442 : a04442.IsHomogeneous 272 := by
  unfold a04442
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha02171.pow 1)))

@[irreducible]
def a04443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00042 ^ 2 * a04420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a04418 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 1 * a00126 ^ 1 * a04442 ^ 1) + (C ((25 : ℂ) / (1728 : ℂ)) * a00000 ^ 1 * a00042 ^ 1 * a04419 ^ 1)
theorem ha04443 : a04443.IsHomogeneous 441 := by
  unfold a04443
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00042.pow 2)).mul (ha04420.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha04418.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04442.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1728 : ℂ))).mul (ha00000.pow 1)).mul (ha00042.pow 1)).mul (ha04419.pow 1)))

@[irreducible]
def a04444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04443 ^ 1) + (C ((3 : ℂ) / (200 : ℂ)) * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00042 ^ 4 * a00100 ^ 4 * a04417 ^ 1)
theorem ha04444 : a04444.IsHomogeneous 441 := by
  unfold a04444
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04443.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (200 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha04417.pow 1)))

@[irreducible]
def a04445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04444 ^ 1)
theorem ha04445 : a04445.IsHomogeneous 441 := by
  unfold a04445
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02173.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04444.pow 1)))

@[irreducible]
def a04446 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a04445 ^ 1)
theorem ha04446 : a04446.IsHomogeneous 867 := by
  unfold a04446
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha02173.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha04445.pow 1)))

@[irreducible]
def a04447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha04447 : a04447.IsHomogeneous 36 := by
  unfold a04447
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04448 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a04447 ^ 1)
theorem ha04448 : a04448.IsHomogeneous 43 := by
  unfold a04448
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha00455.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha04447.pow 1)))

@[irreducible]
def a04449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04448 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00368 ^ 1 * a01041 ^ 1)
theorem ha04449 : a04449.IsHomogeneous 43 := by
  unfold a04449
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04448.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00368.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04450 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04449 ^ 1)
theorem ha04450 : a04450.IsHomogeneous 43 := by
  unfold a04450
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha00455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04449.pow 1)))

@[irreducible]
def a04451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a04447 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04450 ^ 1)
theorem ha04451 : a04451.IsHomogeneous 43 := by
  unfold a04451
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha04447.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04450.pow 1)))

@[irreducible]
def a04452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a04451 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a02177 ^ 1)
theorem ha04452 : a04452.IsHomogeneous 61 := by
  unfold a04452
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha04451.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha02177.pow 1)))

@[irreducible]
def a04453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a02313 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00461 ^ 1 * a00991 ^ 1)
theorem ha04453 : a04453.IsHomogeneous 66 := by
  unfold a04453
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha02313.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00461.pow 1)).mul (ha00991.pow 1)))

@[irreducible]
def a04454 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a04453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a04452 ^ 1)
theorem ha04454 : a04454.IsHomogeneous 73 := by
  unfold a04454
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha04453.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha04452.pow 1)))

@[irreducible]
def a04455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00400 ^ 1 * a01052 ^ 1)
theorem ha04455 : a04455.IsHomogeneous 68 := by
  unfold a04455
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01107.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a04456 : Poly := (C ((-9 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a04455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04454 ^ 1)
theorem ha04456 : a04456.IsHomogeneous 79 := by
  unfold a04456
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha04455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04454.pow 1)))

@[irreducible]
def a04457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a00953 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a02242 ^ 1)
theorem ha04457 : a04457.IsHomogeneous 66 := by
  unfold a04457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha00953.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a04458 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00014 ^ 1 * a04457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04456 ^ 1)
theorem ha04458 : a04458.IsHomogeneous 79 := by
  unfold a04458
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha04457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04456.pow 1)))

@[irreducible]
def a04459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02133 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a04368 ^ 1)
theorem ha04459 : a04459.IsHomogeneous 49 := by
  unfold a04459
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha04368.pow 1)))

@[irreducible]
def a04460 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00126 ^ 1 * a04459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04458 ^ 1)
theorem ha04460 : a04460.IsHomogeneous 85 := by
  unfold a04460
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00126.pow 1)).mul (ha04459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04458.pow 1)))

@[irreducible]
def a04461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04460 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02181 ^ 1)
theorem ha04461 : a04461.IsHomogeneous 91 := by
  unfold a04461
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04460.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02181.pow 1)))

@[irreducible]
def a04462 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00484 ^ 1 * a00996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02327 ^ 1)
theorem ha04462 : a04462.IsHomogeneous 305 := by
  unfold a04462
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00484.pow 1)).mul (ha00996.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a04463 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a01118 ^ 1)
theorem ha04463 : a04463.IsHomogeneous 308 := by
  unfold a04463
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a04464 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a00982 ^ 1)
theorem ha04464 : a04464.IsHomogeneous 256 := by
  unfold a04464
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a04465 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a02166 ^ 1)
theorem ha04465 : a04465.IsHomogeneous 175 := by
  unfold a04465
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04430.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a04466 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a00126 ^ 1 * a04465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a04462 ^ 1) + (C ((25 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a04463 ^ 1)
theorem ha04466 : a04466.IsHomogeneous 309 := by
  unfold a04466
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha04465.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04464.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha04462.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha04463.pow 1)))

@[irreducible]
def a04467 : Poly := (C ((-1 : ℂ) / (200 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 4 * a00100 ^ 5 * a04461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04466 ^ 1)
theorem ha04467 : a04467.IsHomogeneous 309 := by
  unfold a04467
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (200 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 4)).mul (ha00100.pow 5)).mul (ha04461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04466.pow 1)))

@[irreducible]
def a04468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04467 ^ 1)
theorem ha04468 : a04468.IsHomogeneous 309 := by
  unfold a04468
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04467.pow 1)))

@[irreducible]
def a04469 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a04468 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a02183 ^ 1)
theorem ha04469 : a04469.IsHomogeneous 735 := by
  unfold a04469
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha04468.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha02183.pow 1)))

@[irreducible]
def a04470 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00012 ^ 4 * a04446 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 5 * a04346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 1 * a04345 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00001 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 5 * a00042 ^ 4 * a00100 ^ 3 * a00126 ^ 1 * a04340 ^ 1) + (C ((1 : ℂ) / (750 : ℂ)) * a00000 ^ 1 * a00001 ^ 11 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 5 * a00042 ^ 5 * a00100 ^ 6 * a01035 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 2 * a04342 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 2 * a04341 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a04343 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 5 * a00100 ^ 1 * a04344 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 5 * a04469 ^ 1)
theorem ha04470 : a04470.IsHomogeneous 891 := by
  unfold a04470
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00012.pow 4)).mul (ha04446.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha04346.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 1)).mul (ha04345.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00001.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 5)).mul (ha00042.pow 4)).mul (ha00100.pow 3)).mul (ha00126.pow 1)).mul (ha04340.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (750 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 11)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 5)).mul (ha00042.pow 5)).mul (ha00100.pow 6)).mul (ha01035.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 2)).mul (ha04342.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha04341.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha04343.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 1)).mul (ha04344.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha04469.pow 1)))

@[irreducible]
def a04471 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00368 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00368 ^ 1)
theorem ha04471 : a04471.IsHomogeneous 12 := by
  unfold a04471
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a04472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a01122 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a04471 ^ 1)
theorem ha04472 : a04472.IsHomogeneous 31 := by
  unfold a04472
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01122.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04471.pow 1)))

@[irreducible]
def a04473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00042 ^ 1)
theorem ha04473 : a04473.IsHomogeneous 30 := by
  unfold a04473
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a04474 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a04473 ^ 1)
theorem ha04474 : a04474.IsHomogeneous 37 := by
  unfold a04474
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01122.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha04473.pow 1)))

@[irreducible]
def a04475 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04472 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04474 ^ 1)
theorem ha04475 : a04475.IsHomogeneous 37 := by
  unfold a04475
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04474.pow 1)))

@[irreducible]
def a04476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a01122 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a04471 ^ 1)
theorem ha04476 : a04476.IsHomogeneous 31 := by
  unfold a04476
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01122.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04471.pow 1)))

@[irreducible]
def a04477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04472 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04476 ^ 1)
theorem ha04477 : a04477.IsHomogeneous 31 := by
  unfold a04477
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04476.pow 1)))

@[irreducible]
def a04478 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04477 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04475 ^ 1)
theorem ha04478 : a04478.IsHomogeneous 37 := by
  unfold a04478
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04477.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04475.pow 1)))

@[irreducible]
def a04479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00559 ^ 1) + (C ((1 : ℂ) / (270 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00562 ^ 1)
theorem ha04479 : a04479.IsHomogeneous 39 := by
  unfold a04479
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00559.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (270 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00562.pow 1)))

@[irreducible]
def a04480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00559 ^ 1) + (C ((1 : ℂ) / (810 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00562 ^ 1)
theorem ha04480 : a04480.IsHomogeneous 39 := by
  unfold a04480
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00559.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (810 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00562.pow 1)))

@[irreducible]
def a04481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04479 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04480 ^ 1)
theorem ha04481 : a04481.IsHomogeneous 39 := by
  unfold a04481
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04480.pow 1)))

@[irreducible]
def a04482 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a00559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a00582 ^ 1)
theorem ha04482 : a04482.IsHomogeneous 39 := by
  unfold a04482
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha00559.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha00582.pow 1)))

@[irreducible]
def a04483 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04482 ^ 1)
theorem ha04483 : a04483.IsHomogeneous 45 := by
  unfold a04483
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04479.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04482.pow 1)))

@[irreducible]
def a04484 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04483 ^ 1)
theorem ha04484 : a04484.IsHomogeneous 45 := by
  unfold a04484
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04483.pow 1)))

@[irreducible]
def a04485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00516 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00586 ^ 1)
theorem ha04485 : a04485.IsHomogeneous 33 := by
  unfold a04485
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00516.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00586.pow 1)))

@[irreducible]
def a04486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04485 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00586 ^ 1)
theorem ha04486 : a04486.IsHomogeneous 33 := by
  unfold a04486
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04485.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00586.pow 1)))

@[irreducible]
def a04487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04486 ^ 1)
theorem ha04487 : a04487.IsHomogeneous 33 := by
  unfold a04487
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04486.pow 1)))

@[irreducible]
def a04488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00156 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00042 ^ 1 * a00510 ^ 1)
theorem ha04488 : a04488.IsHomogeneous 42 := by
  unfold a04488
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00042.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a04489 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00510 ^ 1)
theorem ha04489 : a04489.IsHomogeneous 24 := by
  unfold a04489
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1)).mul (ha00156.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a04490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04488 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04489 ^ 1) + (C ((1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00591 ^ 1)
theorem ha04490 : a04490.IsHomogeneous 42 := by
  unfold a04490
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04488.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04489.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00591.pow 1)))

@[irreducible]
def a04491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04490 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04489 ^ 1) + (C ((1 : ℂ) / (5832 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00591 ^ 1)
theorem ha04491 : a04491.IsHomogeneous 42 := by
  unfold a04491
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04490.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04489.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5832 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00591.pow 1)))

@[irreducible]
def a04492 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a04491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04484 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 5 * a00014 ^ 1 * a04478 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 2 * a00014 ^ 1 * a04487 ^ 1)
theorem ha04492 : a04492.IsHomogeneous 48 := by
  unfold a04492
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha04491.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04484.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 5)).mul (ha00014.pow 1)).mul (ha04478.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha04487.pow 1)))

@[irreducible]
def a04493 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a01026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02376 ^ 1)
theorem ha04493 : a04493.IsHomogeneous 281 := by
  unfold a04493
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha01026.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a04494 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01180 ^ 1)
theorem ha04494 : a04494.IsHomogeneous 235 := by
  unfold a04494
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00445.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a04495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00931 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00362 ^ 1)
theorem ha04495 : a04495.IsHomogeneous 182 := by
  unfold a04495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00931.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00362.pow 1)))

@[irreducible]
def a04496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00327 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00173 ^ 1)
theorem ha04496 : a04496.IsHomogeneous 127 := by
  unfold a04496
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00173.pow 1)))

@[irreducible]
def a04497 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04494 ^ 1) + (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 6 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 6 * a00100 ^ 3 * a04496 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 2 * a04495 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a04493 ^ 1)
theorem ha04497 : a04497.IsHomogeneous 285 := by
  unfold a04497
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04494.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00100.pow 3)).mul (ha04496.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha04495.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha04493.pow 1)))

@[irreducible]
def a04498 : Poly := (C ((-1 : ℂ) / (60 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 7 * a00100 ^ 5 * a04492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04497 ^ 1)
theorem ha04498 : a04498.IsHomogeneous 285 := by
  unfold a04498
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (60 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 7)).mul (ha00100.pow 5)).mul (ha04492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04497.pow 1)))

@[irreducible]
def a04499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04498 ^ 1)
theorem ha04499 : a04499.IsHomogeneous 285 := by
  unfold a04499
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04498.pow 1)))

@[irreducible]
def a04500 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a04499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a02203 ^ 1)
theorem ha04500 : a04500.IsHomogeneous 843 := by
  unfold a04500
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha04499.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha02203.pow 1)))

@[irreducible]
def a04501 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00134 ^ 2 * a04470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 4 * a00126 ^ 1 * a04500 ^ 1)
theorem ha04501 : a04501.IsHomogeneous 1011 := by
  unfold a04501
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00134.pow 2)).mul (ha04470.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha00126.pow 1)).mul (ha04500.pow 1)))

@[irreducible]
def a04502 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a02376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a01026 ^ 1)
theorem ha04502 : a04502.IsHomogeneous 1374 := by
  unfold a04502
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha02376.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a04503 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 3 * a04502 ^ 1)
theorem ha04503 : a04503.IsHomogeneous 1464 := by
  unfold a04503
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04501.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 3)).mul (ha04502.pow 1)))

@[irreducible]
def a04504 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00937 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a02116 ^ 1)
theorem ha04504 : a04504.IsHomogeneous 1856 := by
  unfold a04504
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00937.pow 1)).mul (ha01180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a04505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04503 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a04504 ^ 1)
theorem ha04505 : a04505.IsHomogeneous 1917 := by
  unfold a04505
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04503.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha04504.pow 1)))

@[irreducible]
def a04506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a00940 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a02212 ^ 1)
theorem ha04506 : a04506.IsHomogeneous 589 := by
  unfold a04506
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha00940.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha02212.pow 1)))

@[irreducible]
def a04507 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a02211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a00940 ^ 1)
theorem ha04507 : a04507.IsHomogeneous 685 := by
  unfold a04507
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha02211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a04508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a00938 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a02207 ^ 1)
theorem ha04508 : a04508.IsHomogeneous 148 := by
  unfold a04508
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha00938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha02207.pow 1)))

@[irreducible]
def a04509 : Poly := (C ((-1 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00595 ^ 1) + (C ((1 : ℂ) / (800 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00712 ^ 1) + (C ((3 : ℂ) / (10 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1)
theorem ha04509 : a04509.IsHomogeneous 78 := by
  unfold a04509
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00595.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (800 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00712.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (10 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a04510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00125 ^ 1 * a04509 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a02207 ^ 1)
theorem ha04510 : a04510.IsHomogeneous 148 := by
  unfold a04510
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00125.pow 1)).mul (ha04509.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha02207.pow 1)))

@[irreducible]
def a04511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04510 ^ 1)
theorem ha04511 : a04511.IsHomogeneous 148 := by
  unfold a04511
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04510.pow 1)))

@[irreducible]
def a04512 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a02209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00713 ^ 1 * a00939 ^ 1)
theorem ha04512 : a04512.IsHomogeneous 151 := by
  unfold a04512
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha02209.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00713.pow 1)).mul (ha00939.pow 1)))

@[irreducible]
def a04513 : Poly := (C ((-5 : ℂ) / (432 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (80 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00712 ^ 1)
theorem ha04513 : a04513.IsHomogeneous 70 := by
  unfold a04513
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (432 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (80 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a04514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00101 ^ 1 * a04513 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00261 ^ 1 * a02209 ^ 1)
theorem ha04514 : a04514.IsHomogeneous 151 := by
  unfold a04514
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00101.pow 1)).mul (ha04513.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00261.pow 1)).mul (ha02209.pow 1)))

@[irreducible]
def a04515 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a04514 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04512 ^ 1)
theorem ha04515 : a04515.IsHomogeneous 151 := by
  unfold a04515
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha04514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04512.pow 1)))

@[irreducible]
def a04516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a04511 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04515 ^ 1)
theorem ha04516 : a04516.IsHomogeneous 153 := by
  unfold a04516
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha04511.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04515.pow 1)))

@[irreducible]
def a04517 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a02211 ^ 1)
theorem ha04517 : a04517.IsHomogeneous 431 := by
  unfold a04517
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04516.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha02211.pow 1)))

@[irreducible]
def a04518 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04517 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04507 ^ 1)
theorem ha04518 : a04518.IsHomogeneous 685 := by
  unfold a04518
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04517.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04507.pow 1)))

@[irreducible]
def a04519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a02212 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a04518 ^ 1)
theorem ha04519 : a04519.IsHomogeneous 764 := by
  unfold a04519
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha02212.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha04518.pow 1)))

@[irreducible]
def a04520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04506 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a04519 ^ 1)
theorem ha04520 : a04520.IsHomogeneous 843 := by
  unfold a04520
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha04519.pow 1)))

@[irreducible]
def a04521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a02213 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04520 ^ 1)
theorem ha04521 : a04521.IsHomogeneous 951 := by
  unfold a04521
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha02213.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04520.pow 1)))

@[irreducible]
def a04522 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a00940 ^ 1)
theorem ha04522 : a04522.IsHomogeneous 708 := by
  unfold a04522
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a04523 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04522 ^ 1)
theorem ha04523 : a04523.IsHomogeneous 1041 := by
  unfold a04523
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04521.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04522.pow 1)))

@[irreducible]
def a04524 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a02213 ^ 1)
theorem ha04524 : a04524.IsHomogeneous 927 := by
  unfold a04524
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a04525 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a00940 ^ 1)
theorem ha04525 : a04525.IsHomogeneous 660 := by
  unfold a04525
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a04526 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a04524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04525 ^ 1)
theorem ha04526 : a04526.IsHomogeneous 993 := by
  unfold a04526
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04524.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04525.pow 1)))

@[irreducible]
def a04527 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a01035 ^ 1)
theorem ha04527 : a04527.IsHomogeneous 1054 := by
  unfold a04527
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a04528 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01290 ^ 1)
theorem ha04528 : a04528.IsHomogeneous 781 := by
  unfold a04528
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a04529 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04527 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04528 ^ 1)
theorem ha04529 : a04529.IsHomogeneous 1114 := by
  unfold a04529
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04527.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04528.pow 1)))

@[irreducible]
def a04530 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a01035 ^ 1)
theorem ha04530 : a04530.IsHomogeneous 994 := by
  unfold a04530
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a04531 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01313 ^ 1)
theorem ha04531 : a04531.IsHomogeneous 697 := by
  unfold a04531
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a04532 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04531 ^ 1)
theorem ha04532 : a04532.IsHomogeneous 1030 := by
  unfold a04532
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04530.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04531.pow 1)))

@[irreducible]
def a04533 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01103 ^ 1)
theorem ha04533 : a04533.IsHomogeneous 1119 := by
  unfold a04533
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02540 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a01103 ^ 1)
theorem ha04534 : a04534.IsHomogeneous 846 := by
  unfold a04534
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02540.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04534 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04533 ^ 1)
theorem ha04535 : a04535.IsHomogeneous 1179 := by
  unfold a04535
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04534.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04533.pow 1)))

@[irreducible]
def a04536 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01118 ^ 1)
theorem ha04536 : a04536.IsHomogeneous 1035 := by
  unfold a04536
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a04537 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02574 ^ 1)
theorem ha04537 : a04537.IsHomogeneous 738 := by
  unfold a04537
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01118.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a04538 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04537 ^ 1)
theorem ha04538 : a04538.IsHomogeneous 1071 := by
  unfold a04538
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04536.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04537.pow 1)))

@[irreducible]
def a04539 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02308 ^ 1)
theorem ha04539 : a04539.IsHomogeneous 1171 := by
  unfold a04539
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha00988.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a04540 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02307 ^ 1)
theorem ha04540 : a04540.IsHomogeneous 436 := by
  unfold a04540
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha00988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02307.pow 1)))

@[irreducible]
def a04541 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00148 ^ 1 * a02413 ^ 1)
theorem ha04541 : a04541.IsHomogeneous 151 := by
  unfold a04541
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a04542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a01264 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00480 ^ 1 * a01041 ^ 1)
theorem ha04542 : a04542.IsHomogeneous 151 := by
  unfold a04542
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha01264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00480.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04543 : Poly := (C ((-45 : ℂ) / (4 : ℂ)) * a04542 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04541 ^ 1)
theorem ha04543 : a04543.IsHomogeneous 151 := by
  unfold a04543
  exact (((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (4 : ℂ))).mul (ha04542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04541.pow 1)))

@[irreducible]
def a04544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00007 ^ 1 * a00014 ^ 4 * a01210 ^ 1) + (C ((25 : ℂ) / (1458 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a04543 ^ 1)
theorem ha04544 : a04544.IsHomogeneous 163 := by
  unfold a04544
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 4)).mul (ha01210.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04543.pow 1)))

@[irreducible]
def a04545 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00389 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01083 ^ 1)
theorem ha04545 : a04545.IsHomogeneous 162 := by
  unfold a04545
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00389.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a04546 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00455 ^ 1 * a01083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02499 ^ 1)
theorem ha04546 : a04546.IsHomogeneous 162 := by
  unfold a04546
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)).mul (ha01083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02499.pow 1)))

@[irreducible]
def a04547 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a04546 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04545 ^ 1)
theorem ha04547 : a04547.IsHomogeneous 162 := by
  unfold a04547
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha04546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04545.pow 1)))

@[irreducible]
def a04548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04544 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a04547 ^ 1)
theorem ha04548 : a04548.IsHomogeneous 163 := by
  unfold a04548
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04544.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha04547.pow 1)))

@[irreducible]
def a04549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02282 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a00976 ^ 1)
theorem ha04549 : a04549.IsHomogeneous 187 := by
  unfold a04549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02282.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha00976.pow 1)))

@[irreducible]
def a04550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00945 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a02227 ^ 1)
theorem ha04550 : a04550.IsHomogeneous 37 := by
  unfold a04550
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha02227.pow 1)))

@[irreducible]
def a04551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha04551 : a04551.IsHomogeneous 6 := by
  unfold a04551
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a04552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00506 ^ 1)
theorem ha04552 : a04552.IsHomogeneous 36 := by
  unfold a04552
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00317 ^ 1)
theorem ha04553 : a04553.IsHomogeneous 27 := by
  unfold a04553
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04552 ^ 1)
theorem ha04554 : a04554.IsHomogeneous 36 := by
  unfold a04554
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04552.pow 1)))

@[irreducible]
def a04555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a04551 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04554 ^ 1)
theorem ha04555 : a04555.IsHomogeneous 41 := by
  unfold a04555
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha04551.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04554.pow 1)))

@[irreducible]
def a04556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04555 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04554 ^ 1)
theorem ha04556 : a04556.IsHomogeneous 41 := by
  unfold a04556
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04554.pow 1)))

@[irreducible]
def a04557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04555 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04556 ^ 1)
theorem ha04557 : a04557.IsHomogeneous 41 := by
  unfold a04557
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04556.pow 1)))

@[irreducible]
def a04558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02227 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a04557 ^ 1)
theorem ha04558 : a04558.IsHomogeneous 47 := by
  unfold a04558
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02227.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha04557.pow 1)))

@[irreducible]
def a04559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a04550 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a04558 ^ 1)
theorem ha04559 : a04559.IsHomogeneous 47 := by
  unfold a04559
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha04550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha04558.pow 1)))

@[irreducible]
def a04560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00506 ^ 1)
theorem ha04560 : a04560.IsHomogeneous 24 := by
  unfold a04560
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1)
theorem ha04561 : a04561.IsHomogeneous 18 := by
  unfold a04561
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a04562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00324 ^ 1)
theorem ha04562 : a04562.IsHomogeneous 18 := by
  unfold a04562
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a04563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04561 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a04562 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a04560 ^ 1)
theorem ha04563 : a04563.IsHomogeneous 24 := by
  unfold a04563
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04561.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha04562.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha04560.pow 1)))

@[irreducible]
def a04564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00042 ^ 1 * a00510 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00130 ^ 1 * a00156 ^ 1)
theorem ha04564 : a04564.IsHomogeneous 42 := by
  unfold a04564
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a04565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00156 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00042 ^ 1)
theorem ha04565 : a04565.IsHomogeneous 36 := by
  unfold a04565
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a04566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00156 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha04566 : a04566.IsHomogeneous 33 := by
  unfold a04566
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04564 ^ 1)
theorem ha04567 : a04567.IsHomogeneous 42 := by
  unfold a04567
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04565.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04564.pow 1)))

@[irreducible]
def a04568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04567 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04563 ^ 1)
theorem ha04568 : a04568.IsHomogeneous 42 := by
  unfold a04568
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04567.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04563.pow 1)))

@[irreducible]
def a04569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04567 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04568 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04563 ^ 1)
theorem ha04569 : a04569.IsHomogeneous 42 := by
  unfold a04569
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04567.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04568.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04563.pow 1)))

@[irreducible]
def a04570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04568 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04563 ^ 1)
theorem ha04570 : a04570.IsHomogeneous 42 := by
  unfold a04570
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04568.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04563.pow 1)))

@[irreducible]
def a04571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04569 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04570 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a04563 ^ 1)
theorem ha04571 : a04571.IsHomogeneous 42 := by
  unfold a04571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04570.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04563.pow 1)))

@[irreducible]
def a04572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00176 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00324 ^ 1)
theorem ha04572 : a04572.IsHomogeneous 18 := by
  unfold a04572
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00176.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a04573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00176 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00570 ^ 1)
theorem ha04573 : a04573.IsHomogeneous 24 := by
  unfold a04573
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00570.pow 1)))

@[irreducible]
def a04574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04573 ^ 1)
theorem ha04574 : a04574.IsHomogeneous 24 := by
  unfold a04574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04573.pow 1)))

@[irreducible]
def a04575 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04571 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04559 ^ 1) + (C ((1 : ℂ) / (270 : ℂ)) * a00000 ^ 13 * a00001 ^ 3 * a00002 ^ 1 * a00003 ^ 3 * a00004 ^ 3 * a04574 ^ 1)
theorem ha04575 : a04575.IsHomogeneous 47 := by
  unfold a04575
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04571.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04559.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (270 : ℂ))).mul (ha00000.pow 13)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha04574.pow 1)))

@[irreducible]
def a04576 : Poly := (C ((-5 : ℂ) / (216 : ℂ)) * a00100 ^ 1 * a04575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02236 ^ 1)
theorem ha04576 : a04576.IsHomogeneous 83 := by
  unfold a04576
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (216 : ℂ))).mul (ha00100.pow 1)).mul (ha04575.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02236.pow 1)))

@[irreducible]
def a04577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00260 ^ 1 * a02236 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00829 ^ 1 * a00950 ^ 1)
theorem ha04577 : a04577.IsHomogeneous 121 := by
  unfold a04577
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00829.pow 1)).mul (ha00950.pow 1)))

@[irreducible]
def a04578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04577 ^ 1)
theorem ha04578 : a04578.IsHomogeneous 121 := by
  unfold a04578
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04577.pow 1)))

@[irreducible]
def a04579 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00484 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a02432 ^ 1)
theorem ha04579 : a04579.IsHomogeneous 118 := by
  unfold a04579
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00484.pow 1)).mul (ha01048.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha02432.pow 1)))

@[irreducible]
def a04580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00484 ^ 1 * a01048 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00370 ^ 1 * a01275 ^ 1)
theorem ha04580 : a04580.IsHomogeneous 121 := by
  unfold a04580
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00484.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00370.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a04581 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a04580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04579 ^ 1)
theorem ha04581 : a04581.IsHomogeneous 121 := by
  unfold a04581
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha04580.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04579.pow 1)))

@[irreducible]
def a04582 : Poly := (C ((-25 : ℂ) / (36 : ℂ)) * a04581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04578 ^ 1)
theorem ha04582 : a04582.IsHomogeneous 121 := by
  unfold a04582
  exact (((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (36 : ℂ))).mul (ha04581.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04578.pow 1)))

@[irreducible]
def a04583 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00393 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a01092 ^ 1)
theorem ha04583 : a04583.IsHomogeneous 148 := by
  unfold a04583
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00393.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a04584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00137 ^ 1 * a02520 ^ 1)
theorem ha04584 : a04584.IsHomogeneous 157 := by
  unfold a04584
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00137.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a04585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04584 ^ 1)
theorem ha04585 : a04585.IsHomogeneous 157 := by
  unfold a04585
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04584.pow 1)))

@[irreducible]
def a04586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04585 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a04582 ^ 1)
theorem ha04586 : a04586.IsHomogeneous 157 := by
  unfold a04586
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04585.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha04582.pow 1)))

@[irreducible]
def a04587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00975 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a02280 ^ 1)
theorem ha04587 : a04587.IsHomogeneous 133 := by
  unfold a04587
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha02280.pow 1)))

@[irreducible]
def a04588 : Poly := (C ((-7 : ℂ) / (240 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00006 ^ 1 * a00007 ^ 1 * a00782 ^ 1) + (C ((1 : ℂ) / (1080 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00007 ^ 1)
theorem ha04588 : a04588.IsHomogeneous 22 := by
  unfold a04588
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (240 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00321.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00782.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1080 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00007.pow 1)))

@[irreducible]
def a04589 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a02242 ^ 1)
theorem ha04589 : a04589.IsHomogeneous 118 := by
  unfold a04589
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04588.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a04590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00301 ^ 1 * a02242 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00819 ^ 1 * a00953 ^ 1)
theorem ha04590 : a04590.IsHomogeneous 126 := by
  unfold a04590
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00819.pow 1)).mul (ha00953.pow 1)))

@[irreducible]
def a04591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a04589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04590 ^ 1)
theorem ha04591 : a04591.IsHomogeneous 126 := by
  unfold a04591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha04589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04590.pow 1)))

@[irreducible]
def a04592 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a02441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a01052 ^ 1)
theorem ha04592 : a04592.IsHomogeneous 120 := by
  unfold a04592
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha02441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a04593 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00476 ^ 1 * a01052 ^ 1)
theorem ha04593 : a04593.IsHomogeneous 128 := by
  unfold a04593
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a04594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a04592 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04593 ^ 1)
theorem ha04594 : a04594.IsHomogeneous 128 := by
  unfold a04594
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha04592.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04593.pow 1)))

@[irreducible]
def a04595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04594 ^ 1) + (C ((48 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a04591 ^ 1)
theorem ha04595 : a04595.IsHomogeneous 133 := by
  unfold a04595
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04594.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha04591.pow 1)))

@[irreducible]
def a04596 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a01079 ^ 1)
theorem ha04596 : a04596.IsHomogeneous 117 := by
  unfold a04596
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a04597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a01079 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00138 ^ 1 * a02493 ^ 1)
theorem ha04597 : a04597.IsHomogeneous 126 := by
  unfold a04597
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha01079.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00138.pow 1)).mul (ha02493.pow 1)))

@[irreducible]
def a04598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04597 ^ 1)
theorem ha04598 : a04598.IsHomogeneous 126 := by
  unfold a04598
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04597.pow 1)))

@[irreducible]
def a04599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04595 ^ 1) + (C ((32 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a04598 ^ 1)
theorem ha04599 : a04599.IsHomogeneous 133 := by
  unfold a04599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04595.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha04598.pow 1)))

@[irreducible]
def a04600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a02278 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a00974 ^ 1)
theorem ha04600 : a04600.IsHomogeneous 112 := by
  unfold a04600
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha02278.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha00974.pow 1)))

@[irreducible]
def a04601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a00958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02252 ^ 1)
theorem ha04601 : a04601.IsHomogeneous 84 := by
  unfold a04601
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha00958.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a04602 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00368 ^ 1)
theorem ha04602 : a04602.IsHomogeneous 12 := by
  unfold a04602
  exact (((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a04603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02413 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01041 ^ 1)
theorem ha04603 : a04603.IsHomogeneous 18 := by
  unfold a04603
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01041.pow 1)))

@[irreducible]
def a04604 : Poly := (C ((-45 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a04602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04603 ^ 1)
theorem ha04604 : a04604.IsHomogeneous 18 := by
  unfold a04604
  exact ((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha04602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04603.pow 1)))

@[irreducible]
def a04605 : Poly := (C ((-1 : ℂ) / (243 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04604 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01236 ^ 1)
theorem ha04605 : a04605.IsHomogeneous 46 := by
  unfold a04605
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (243 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04604.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01236.pow 1)))

@[irreducible]
def a04606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00455 ^ 1)
theorem ha04606 : a04606.IsHomogeneous 18 := by
  unfold a04606
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1)
theorem ha04607 : a04607.IsHomogeneous 18 := by
  unfold a04607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)))

end CycleQ2Concrete
