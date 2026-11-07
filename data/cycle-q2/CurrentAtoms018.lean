import Proposal.CurrentAtoms017

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a06400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06388 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06399 ^ 1)
theorem ha06400 : a06400.IsHomogeneous 30 := by
  unfold a06400
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06388.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06399.pow 1)))

@[irreducible]
def a06401 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00058 ^ 1)
theorem ha06401 : a06401.IsHomogeneous 18 := by
  unfold a06401
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)))

@[irreducible]
def a06402 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06392 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a06401 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06396 ^ 1)
theorem ha06402 : a06402.IsHomogeneous 24 := by
  unfold a06402
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha06401.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06396.pow 1)))

@[irreducible]
def a06403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06393 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06402 ^ 1)
theorem ha06403 : a06403.IsHomogeneous 30 := by
  unfold a06403
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06393.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06402.pow 1)))

@[irreducible]
def a06404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06394 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06403 ^ 1)
theorem ha06404 : a06404.IsHomogeneous 30 := by
  unfold a06404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06394.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06400.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06403.pow 1)))

@[irreducible]
def a06405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a00632 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a00864 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1 * a01575 ^ 1)
theorem ha06405 : a06405.IsHomogeneous 30 := by
  unfold a06405
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha00864.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a00864 ^ 1)
theorem ha06406 : a06406.IsHomogeneous 30 := by
  unfold a06406
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06405 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a06406 ^ 1)
theorem ha06407 : a06407.IsHomogeneous 30 := by
  unfold a06407
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06405.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha06406.pow 1)))

@[irreducible]
def a06408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a01575 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1)
theorem ha06408 : a06408.IsHomogeneous 18 := by
  unfold a06408
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06405 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06408 ^ 1)
theorem ha06409 : a06409.IsHomogeneous 30 := by
  unfold a06409
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06405.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06408.pow 1)))

@[irreducible]
def a06410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06388 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06407 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06409 ^ 1)
theorem ha06410 : a06410.IsHomogeneous 30 := by
  unfold a06410
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06407.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06409.pow 1)))

@[irreducible]
def a06411 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a02007 ^ 1)
theorem ha06411 : a06411.IsHomogeneous 30 := by
  unfold a06411
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha04085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a06412 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a06406 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06411 ^ 1)
theorem ha06412 : a06412.IsHomogeneous 30 := by
  unfold a06412
  exact ((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha06406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06390.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06411.pow 1)))

@[irreducible]
def a06413 : Poly := (C ((-1 : ℂ) / (14 : ℂ)) * a06412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06391 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06407 ^ 1)
theorem ha06413 : a06413.IsHomogeneous 30 := by
  unfold a06413
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (14 : ℂ))).mul (ha06412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06391.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06407.pow 1)))

@[irreducible]
def a06414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06394 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06410 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06413 ^ 1)
theorem ha06414 : a06414.IsHomogeneous 30 := by
  unfold a06414
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06394.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06410.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06413.pow 1)))

@[irreducible]
def a06415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha06415 : a06415.IsHomogeneous 6 := by
  unfold a06415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a06416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00324 ^ 1)
theorem ha06416 : a06416.IsHomogeneous 6 := by
  unfold a06416
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a06417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06415 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06416 ^ 1)
theorem ha06417 : a06417.IsHomogeneous 6 := by
  unfold a06417
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06416.pow 1)))

@[irreducible]
def a06418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01603 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06416 ^ 1)
theorem ha06418 : a06418.IsHomogeneous 6 := by
  unfold a06418
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01603.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06416.pow 1)))

@[irreducible]
def a06419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06417 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06418 ^ 1)
theorem ha06419 : a06419.IsHomogeneous 6 := by
  unfold a06419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06418.pow 1)))

@[irreducible]
def a06420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06415 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha06420 : a06420.IsHomogeneous 6 := by
  unfold a06420
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a06421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06420 ^ 1)
theorem ha06421 : a06421.IsHomogeneous 6 := by
  unfold a06421
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06420.pow 1)))

@[irreducible]
def a06422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06421 ^ 1)
theorem ha06422 : a06422.IsHomogeneous 6 := by
  unfold a06422
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06421.pow 1)))

@[irreducible]
def a06423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01847 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06420 ^ 1)
theorem ha06423 : a06423.IsHomogeneous 6 := by
  unfold a06423
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06420.pow 1)))

@[irreducible]
def a06424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06421 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a06423 ^ 1)
theorem ha06424 : a06424.IsHomogeneous 6 := by
  unfold a06424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha06423.pow 1)))

@[irreducible]
def a06425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06424 ^ 1)
theorem ha06425 : a06425.IsHomogeneous 6 := by
  unfold a06425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06424.pow 1)))

@[irreducible]
def a06426 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a06425 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06152 ^ 1)
theorem ha06426 : a06426.IsHomogeneous 6 := by
  unfold a06426
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha06425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06152.pow 1)))

@[irreducible]
def a06427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06426 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a03363 ^ 1)
theorem ha06427 : a06427.IsHomogeneous 18 := by
  unfold a06427
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a06428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06398 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06427 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06408 ^ 1)
theorem ha06428 : a06428.IsHomogeneous 24 := by
  unfold a06428
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06398.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06427.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06408.pow 1)))

@[irreducible]
def a06429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06399 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06409 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06428 ^ 1)
theorem ha06429 : a06429.IsHomogeneous 30 := by
  unfold a06429
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06399.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06409.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06428.pow 1)))

@[irreducible]
def a06430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06410 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06429 ^ 1)
theorem ha06430 : a06430.IsHomogeneous 30 := by
  unfold a06430
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06400.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06410.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06429.pow 1)))

@[irreducible]
def a06431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06430 ^ 1)
theorem ha06431 : a06431.IsHomogeneous 30 := by
  unfold a06431
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06414.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06430.pow 1)))

@[irreducible]
def a06432 : Poly := (C ((-7 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a06431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a06049 ^ 1)
theorem ha06432 : a06432.IsHomogeneous 43 := by
  unfold a06432
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha06431.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha06049.pow 1)))

@[irreducible]
def a06433 : Poly := (C ((-14 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a06431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06432 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a06049 ^ 1)
theorem ha06433 : a06433.IsHomogeneous 43 := by
  unfold a06433
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha06431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06432.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha06049.pow 1)))

@[irreducible]
def a06434 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a06384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06288 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a06433 ^ 1)
theorem ha06434 : a06434.IsHomogeneous 54 := by
  unfold a06434
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha06384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06288.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha06433.pow 1)))

@[irreducible]
def a06435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01473 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00577 ^ 1 * a00865 ^ 1)
theorem ha06435 : a06435.IsHomogeneous 45 := by
  unfold a06435
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00577.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a03191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01473 ^ 1)
theorem ha06436 : a06436.IsHomogeneous 45 := by
  unfold a06436
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a06437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06436 ^ 1)
theorem ha06437 : a06437.IsHomogeneous 45 := by
  unfold a06437
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06436.pow 1)))

@[irreducible]
def a06438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00179 ^ 1 * a02008 ^ 1)
theorem ha06438 : a06438.IsHomogeneous 45 := by
  unfold a06438
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06435 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06438 ^ 1)
theorem ha06439 : a06439.IsHomogeneous 45 := by
  unfold a06439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06438.pow 1)))

@[irreducible]
def a06440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06437 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06439 ^ 1)
theorem ha06440 : a06440.IsHomogeneous 45 := by
  unfold a06440
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06437.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06439.pow 1)))

@[irreducible]
def a06441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a04086 ^ 1)
theorem ha06441 : a06441.IsHomogeneous 36 := by
  unfold a06441
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a06442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06438 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06441 ^ 1)
theorem ha06442 : a06442.IsHomogeneous 45 := by
  unfold a06442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06438.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06441.pow 1)))

@[irreducible]
def a06443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06439 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06442 ^ 1)
theorem ha06443 : a06443.IsHomogeneous 45 := by
  unfold a06443
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06439.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06442.pow 1)))

@[irreducible]
def a06444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06443 ^ 1)
theorem ha06444 : a06444.IsHomogeneous 45 := by
  unfold a06444
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06443.pow 1)))

@[irreducible]
def a06445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a06158 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03191 ^ 1)
theorem ha06445 : a06445.IsHomogeneous 42 := by
  unfold a06445
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha06158.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a06446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06436 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a06445 ^ 1)
theorem ha06446 : a06446.IsHomogeneous 45 := by
  unfold a06446
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06436.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha06445.pow 1)))

@[irreducible]
def a06447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06437 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06446 ^ 1)
theorem ha06447 : a06447.IsHomogeneous 45 := by
  unfold a06447
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06437.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06446.pow 1)))

@[irreducible]
def a06448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06447 ^ 1)
theorem ha06448 : a06448.IsHomogeneous 45 := by
  unfold a06448
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06447.pow 1)))

@[irreducible]
def a06449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06444 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06448 ^ 1)
theorem ha06449 : a06449.IsHomogeneous 45 := by
  unfold a06449
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06448.pow 1)))

@[irreducible]
def a06450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a06065 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06449 ^ 1)
theorem ha06450 : a06450.IsHomogeneous 50 := by
  unfold a06450
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha06065.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06449.pow 1)))

@[irreducible]
def a06451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06450 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06449 ^ 1)
theorem ha06451 : a06451.IsHomogeneous 50 := by
  unfold a06451
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06450.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06449.pow 1)))

@[irreducible]
def a06452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01617 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00655 ^ 1 * a01327 ^ 1)
theorem ha06452 : a06452.IsHomogeneous 45 := by
  unfold a06452
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01617.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00655.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a01327 ^ 1)
theorem ha06453 : a06453.IsHomogeneous 42 := by
  unfold a06453
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06452 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a06453 ^ 1)
theorem ha06454 : a06454.IsHomogeneous 45 := by
  unfold a06454
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06452.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha06453.pow 1)))

@[irreducible]
def a06455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a03432 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01617 ^ 1)
theorem ha06455 : a06455.IsHomogeneous 45 := by
  unfold a06455
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha03432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a06456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06452 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06455 ^ 1)
theorem ha06456 : a06456.IsHomogeneous 45 := by
  unfold a06456
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06452.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06455.pow 1)))

@[irreducible]
def a06457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06454 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06456 ^ 1)
theorem ha06457 : a06457.IsHomogeneous 45 := by
  unfold a06457
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06454.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06456.pow 1)))

@[irreducible]
def a06458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a05754 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00218 ^ 1 * a02935 ^ 1)
theorem ha06458 : a06458.IsHomogeneous 42 := by
  unfold a06458
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha05754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00218.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06453 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a06458 ^ 1)
theorem ha06459 : a06459.IsHomogeneous 42 := by
  unfold a06459
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06453.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha06458.pow 1)))

@[irreducible]
def a06460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06454 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a06459 ^ 1)
theorem ha06460 : a06460.IsHomogeneous 45 := by
  unfold a06460
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06454.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha06459.pow 1)))

@[irreducible]
def a06461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06460 ^ 1)
theorem ha06461 : a06461.IsHomogeneous 45 := by
  unfold a06461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06460.pow 1)))

@[irreducible]
def a06462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha06462 : a06462.IsHomogeneous 27 := by
  unfold a06462
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a06463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha06463 : a06463.IsHomogeneous 24 := by
  unfold a06463
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a06464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1)
theorem ha06464 : a06464.IsHomogeneous 30 := by
  unfold a06464
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)))

@[irreducible]
def a06465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06464 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06462 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06463 ^ 1)
theorem ha06465 : a06465.IsHomogeneous 30 := by
  unfold a06465
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06464.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06462.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06463.pow 1)))

@[irreducible]
def a06466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00317 ^ 1)
theorem ha06466 : a06466.IsHomogeneous 21 := by
  unfold a06466
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a06467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00317 ^ 1)
theorem ha06467 : a06467.IsHomogeneous 27 := by
  unfold a06467
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)))

@[irreducible]
def a06468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06462 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a06467 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06466 ^ 1)
theorem ha06468 : a06468.IsHomogeneous 27 := by
  unfold a06468
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha06467.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06466.pow 1)))

@[irreducible]
def a06469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06463 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06466 ^ 1)
theorem ha06469 : a06469.IsHomogeneous 24 := by
  unfold a06469
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06463.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06466.pow 1)))

@[irreducible]
def a06470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06465 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06468 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06469 ^ 1)
theorem ha06470 : a06470.IsHomogeneous 30 := by
  unfold a06470
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06465.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06468.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06469.pow 1)))

@[irreducible]
def a06471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1)
theorem ha06471 : a06471.IsHomogeneous 27 := by
  unfold a06471
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00317 ^ 1)
theorem ha06472 : a06472.IsHomogeneous 27 := by
  unfold a06472
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06462 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06472 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06471 ^ 1)
theorem ha06473 : a06473.IsHomogeneous 27 := by
  unfold a06473
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06472.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06471.pow 1)))

@[irreducible]
def a06474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1)
theorem ha06474 : a06474.IsHomogeneous 30 := by
  unfold a06474
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06464 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06474 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06472 ^ 1)
theorem ha06475 : a06475.IsHomogeneous 30 := by
  unfold a06475
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06474.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06472.pow 1)))

@[irreducible]
def a06476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06475 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06473 ^ 1)
theorem ha06476 : a06476.IsHomogeneous 30 := by
  unfold a06476
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06475.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06473.pow 1)))

@[irreducible]
def a06477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a02008 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00865 ^ 1)
theorem ha06477 : a06477.IsHomogeneous 27 := by
  unfold a06477
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06467 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06471 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06477 ^ 1)
theorem ha06478 : a06478.IsHomogeneous 27 := by
  unfold a06478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06471.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06477.pow 1)))

@[irreducible]
def a06479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06468 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06473 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a06478 ^ 1)
theorem ha06479 : a06479.IsHomogeneous 27 := by
  unfold a06479
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06468.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06473.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha06478.pow 1)))

@[irreducible]
def a06480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06476 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06479 ^ 1)
theorem ha06480 : a06480.IsHomogeneous 30 := by
  unfold a06480
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06476.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06479.pow 1)))

@[irreducible]
def a06481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00317 ^ 1)
theorem ha06481 : a06481.IsHomogeneous 27 := by
  unfold a06481
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)))

@[irreducible]
def a06482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00317 ^ 1)
theorem ha06482 : a06482.IsHomogeneous 27 := by
  unfold a06482
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06481 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06482 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06466 ^ 1)
theorem ha06483 : a06483.IsHomogeneous 27 := by
  unfold a06483
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06482.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06466.pow 1)))

@[irreducible]
def a06484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00865 ^ 1)
theorem ha06484 : a06484.IsHomogeneous 30 := by
  unfold a06484
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06484 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06467 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a06481 ^ 1)
theorem ha06485 : a06485.IsHomogeneous 30 := by
  unfold a06485
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06467.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha06481.pow 1)))

@[irreducible]
def a06486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06485 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06468 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a06483 ^ 1)
theorem ha06486 : a06486.IsHomogeneous 30 := by
  unfold a06486
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06485.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06468.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha06483.pow 1)))

@[irreducible]
def a06487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00129 ^ 1)
theorem ha06487 : a06487.IsHomogeneous 30 := by
  unfold a06487
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06487 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06482 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06463 ^ 1)
theorem ha06488 : a06488.IsHomogeneous 30 := by
  unfold a06488
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06487.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06482.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06463.pow 1)))

@[irreducible]
def a06489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06488 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06469 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06483 ^ 1)
theorem ha06489 : a06489.IsHomogeneous 30 := by
  unfold a06489
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06488.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06469.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06483.pow 1)))

@[irreducible]
def a06490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06470 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06486 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a06489 ^ 1)
theorem ha06490 : a06490.IsHomogeneous 30 := by
  unfold a06490
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06486.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha06489.pow 1)))

@[irreducible]
def a06491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02008 ^ 1)
theorem ha06491 : a06491.IsHomogeneous 30 := by
  unfold a06491
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06484 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06491 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06477 ^ 1)
theorem ha06492 : a06492.IsHomogeneous 30 := by
  unfold a06492
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06491.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06477.pow 1)))

@[irreducible]
def a06493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06492 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06478 ^ 1)
theorem ha06493 : a06493.IsHomogeneous 30 := by
  unfold a06493
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06492.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06478.pow 1)))

@[irreducible]
def a06494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06486 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06493 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06479 ^ 1)
theorem ha06494 : a06494.IsHomogeneous 30 := by
  unfold a06494
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06486.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06493.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06479.pow 1)))

@[irreducible]
def a06495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06490 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06494 ^ 1)
theorem ha06495 : a06495.IsHomogeneous 30 := by
  unfold a06495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06490.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06494.pow 1)))

@[irreducible]
def a06496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01607 ^ 1)
theorem ha06496 : a06496.IsHomogeneous 12 := by
  unfold a06496
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01607.pow 1)))

@[irreducible]
def a06497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00649 ^ 1)
theorem ha06497 : a06497.IsHomogeneous 12 := by
  unfold a06497
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a06498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06496 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06497 ^ 1)
theorem ha06498 : a06498.IsHomogeneous 12 := by
  unfold a06498
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06497.pow 1)))

@[irreducible]
def a06499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00032 ^ 1)
theorem ha06499 : a06499.IsHomogeneous 6 := by
  unfold a06499
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)))

@[irreducible]
def a06500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a06499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06497 ^ 1)
theorem ha06500 : a06500.IsHomogeneous 12 := by
  unfold a06500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha06499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06497.pow 1)))

@[irreducible]
def a06501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06498 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06500 ^ 1)
theorem ha06501 : a06501.IsHomogeneous 12 := by
  unfold a06501
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06500.pow 1)))

@[irreducible]
def a06502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01607 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a03417 ^ 1)
theorem ha06502 : a06502.IsHomogeneous 12 := by
  unfold a06502
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha03417.pow 1)))

@[irreducible]
def a06503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06496 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06502 ^ 1)
theorem ha06503 : a06503.IsHomogeneous 12 := by
  unfold a06503
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06502.pow 1)))

@[irreducible]
def a06504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06503 ^ 1)
theorem ha06504 : a06504.IsHomogeneous 12 := by
  unfold a06504
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06503.pow 1)))

@[irreducible]
def a06505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06504 ^ 1)
theorem ha06505 : a06505.IsHomogeneous 12 := by
  unfold a06505
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06501.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06504.pow 1)))

@[irreducible]
def a06506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a01570 ^ 1)
theorem ha06506 : a06506.IsHomogeneous 6 := by
  unfold a06506
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha01570.pow 1)))

@[irreducible]
def a06507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01571 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a06506 ^ 1)
theorem ha06507 : a06507.IsHomogeneous 6 := by
  unfold a06507
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01571.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha06506.pow 1)))

@[irreducible]
def a06508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06506 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a06507 ^ 1)
theorem ha06508 : a06508.IsHomogeneous 6 := by
  unfold a06508
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha06507.pow 1)))

@[irreducible]
def a06509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a06508 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03417 ^ 1)
theorem ha06509 : a06509.IsHomogeneous 12 := by
  unfold a06509
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha06508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03417.pow 1)))

@[irreducible]
def a06510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06502 ^ 1) + (C ((168 : ℂ) / (5 : ℂ)) * a06509 ^ 1)
theorem ha06510 : a06510.IsHomogeneous 12 := by
  unfold a06510
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06502.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((168 : ℂ) / (5 : ℂ))).mul (ha06509.pow 1)))

@[irreducible]
def a06511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06503 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06510 ^ 1)
theorem ha06511 : a06511.IsHomogeneous 12 := by
  unfold a06511
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06510.pow 1)))

@[irreducible]
def a06512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06511 ^ 1)
theorem ha06512 : a06512.IsHomogeneous 12 := by
  unfold a06512
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06511.pow 1)))

@[irreducible]
def a06513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06505 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06512 ^ 1)
theorem ha06513 : a06513.IsHomogeneous 12 := by
  unfold a06513
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06505.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06512.pow 1)))

@[irreducible]
def a06514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1)
theorem ha06514 : a06514.IsHomogeneous 12 := by
  unfold a06514
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha01469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)))

@[irreducible]
def a06515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00574 ^ 1)
theorem ha06515 : a06515.IsHomogeneous 12 := by
  unfold a06515
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00574.pow 1)))

@[irreducible]
def a06516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06514 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a06515 ^ 1)
theorem ha06516 : a06516.IsHomogeneous 12 := by
  unfold a06516
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha06515.pow 1)))

@[irreducible]
def a06517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a03186 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00324 ^ 1 * a01469 ^ 1)
theorem ha06517 : a06517.IsHomogeneous 12 := by
  unfold a06517
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00324.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a06518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06514 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06517 ^ 1)
theorem ha06518 : a06518.IsHomogeneous 12 := by
  unfold a06518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06517.pow 1)))

@[irreducible]
def a06519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06518 ^ 1)
theorem ha06519 : a06519.IsHomogeneous 12 := by
  unfold a06519
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06518.pow 1)))

@[irreducible]
def a06520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00025 ^ 1)
theorem ha06520 : a06520.IsHomogeneous 6 := by
  unfold a06520
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00025.pow 1)))

@[irreducible]
def a06521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a06520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06515 ^ 1)
theorem ha06521 : a06521.IsHomogeneous 12 := by
  unfold a06521
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha06520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06515.pow 1)))

@[irreducible]
def a06522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06516 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a06521 ^ 1)
theorem ha06522 : a06522.IsHomogeneous 12 := by
  unfold a06522
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha06521.pow 1)))

@[irreducible]
def a06523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06522 ^ 1)
theorem ha06523 : a06523.IsHomogeneous 12 := by
  unfold a06523
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06522.pow 1)))

@[irreducible]
def a06524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a06152 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a03186 ^ 1)
theorem ha06524 : a06524.IsHomogeneous 12 := by
  unfold a06524
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha06152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a06525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06517 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06524 ^ 1)
theorem ha06525 : a06525.IsHomogeneous 12 := by
  unfold a06525
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06517.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06524.pow 1)))

@[irreducible]
def a06526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06518 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06525 ^ 1)
theorem ha06526 : a06526.IsHomogeneous 12 := by
  unfold a06526
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06525.pow 1)))

@[irreducible]
def a06527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06526 ^ 1)
theorem ha06527 : a06527.IsHomogeneous 12 := by
  unfold a06527
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06526.pow 1)))

@[irreducible]
def a06528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06527 ^ 1)
theorem ha06528 : a06528.IsHomogeneous 12 := by
  unfold a06528
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06523.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06527.pow 1)))

@[irreducible]
def a06529 : Poly := (C ((-7 : ℂ) / (162 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06513 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06495 ^ 1) + (C ((49 : ℂ) / (90 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06528 ^ 1)
theorem ha06529 : a06529.IsHomogeneous 30 := by
  unfold a06529
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (162 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06495.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((49 : ℂ) / (90 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06528.pow 1)))

@[irreducible]
def a06530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a03432 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06529 ^ 1)
theorem ha06530 : a06530.IsHomogeneous 39 := by
  unfold a06530
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha03432.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06529.pow 1)))

@[irreducible]
def a06531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06455 ^ 1)
theorem ha06531 : a06531.IsHomogeneous 45 := by
  unfold a06531
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06455.pow 1)))

@[irreducible]
def a06532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06456 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06531 ^ 1)
theorem ha06532 : a06532.IsHomogeneous 45 := by
  unfold a06532
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06531.pow 1)))

@[irreducible]
def a06533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06532 ^ 1)
theorem ha06533 : a06533.IsHomogeneous 45 := by
  unfold a06533
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06532.pow 1)))

@[irreducible]
def a06534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06533 ^ 1)
theorem ha06534 : a06534.IsHomogeneous 45 := by
  unfold a06534
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06533.pow 1)))

@[irreducible]
def a06535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a06065 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06534 ^ 1)
theorem ha06535 : a06535.IsHomogeneous 50 := by
  unfold a06535
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha06065.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06534.pow 1)))

@[irreducible]
def a06536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06535 ^ 1)
theorem ha06536 : a06536.IsHomogeneous 50 := by
  unfold a06536
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06450.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06535.pow 1)))

@[irreducible]
def a06537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06536 ^ 1)
theorem ha06537 : a06537.IsHomogeneous 50 := by
  unfold a06537
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06536.pow 1)))

@[irreducible]
def a06538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06451 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06449 ^ 1)
theorem ha06538 : a06538.IsHomogeneous 50 := by
  unfold a06538
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06451.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06449.pow 1)))

@[irreducible]
def a06539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06538 ^ 1)
theorem ha06539 : a06539.IsHomogeneous 50 := by
  unfold a06539
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06538.pow 1)))

@[irreducible]
def a06540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00547 ^ 1)
theorem ha06540 : a06540.IsHomogeneous 39 := by
  unfold a06540
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00547 ^ 1)
theorem ha06541 : a06541.IsHomogeneous 45 := by
  unfold a06541
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a00317 ^ 1)
theorem ha06542 : a06542.IsHomogeneous 45 := by
  unfold a06542
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06541 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06542 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a06540 ^ 1)
theorem ha06543 : a06543.IsHomogeneous 45 := by
  unfold a06543
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06542.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha06540.pow 1)))

@[irreducible]
def a06544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00547 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00547 ^ 1)
theorem ha06544 : a06544.IsHomogeneous 42 := by
  unfold a06544
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00547 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1)
theorem ha06545 : a06545.IsHomogeneous 42 := by
  unfold a06545
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a06546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06544 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06545 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06540 ^ 1)
theorem ha06546 : a06546.IsHomogeneous 42 := by
  unfold a06546
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06545.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06540.pow 1)))

@[irreducible]
def a06547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a01412 ^ 1)
theorem ha06547 : a06547.IsHomogeneous 42 := by
  unfold a06547
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01412.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a06548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06541 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a06547 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06544 ^ 1)
theorem ha06548 : a06548.IsHomogeneous 45 := by
  unfold a06548
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06541.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha06547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06544.pow 1)))

@[irreducible]
def a06549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06548 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06546 ^ 1)
theorem ha06549 : a06549.IsHomogeneous 45 := by
  unfold a06549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06543.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06548.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06546.pow 1)))

@[irreducible]
def a06550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1)
theorem ha06550 : a06550.IsHomogeneous 33 := by
  unfold a06550
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1)
theorem ha06551 : a06551.IsHomogeneous 33 := by
  unfold a06551
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06540 ^ 1)
theorem ha06552 : a06552.IsHomogeneous 39 := by
  unfold a06552
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06550.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06551.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06540.pow 1)))

@[irreducible]
def a06553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00865 ^ 1)
theorem ha06553 : a06553.IsHomogeneous 39 := by
  unfold a06553
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06542 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06550 ^ 1)
theorem ha06554 : a06554.IsHomogeneous 45 := by
  unfold a06554
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06542.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06550.pow 1)))

@[irreducible]
def a06555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06543 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06554 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a06552 ^ 1)
theorem ha06555 : a06555.IsHomogeneous 45 := by
  unfold a06555
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06543.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06554.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha06552.pow 1)))

@[irreducible]
def a06556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha06556 : a06556.IsHomogeneous 36 := by
  unfold a06556
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06545 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06551 ^ 1)
theorem ha06557 : a06557.IsHomogeneous 42 := by
  unfold a06557
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06545.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06551.pow 1)))

@[irreducible]
def a06558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06546 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06557 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06552 ^ 1)
theorem ha06558 : a06558.IsHomogeneous 42 := by
  unfold a06558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06557.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06552.pow 1)))

@[irreducible]
def a06559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06555 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06558 ^ 1)
theorem ha06559 : a06559.IsHomogeneous 45 := by
  unfold a06559
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06558.pow 1)))

@[irreducible]
def a06560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00317 ^ 1 * a01412 ^ 1)
theorem ha06560 : a06560.IsHomogeneous 45 := by
  unfold a06560
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a06561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a01412 ^ 1)
theorem ha06561 : a06561.IsHomogeneous 39 := by
  unfold a06561
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a06562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06541 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06561 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06560 ^ 1)
theorem ha06562 : a06562.IsHomogeneous 45 := by
  unfold a06562
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06541.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06561.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06560.pow 1)))

@[irreducible]
def a06563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a02008 ^ 1)
theorem ha06563 : a06563.IsHomogeneous 45 := by
  unfold a06563
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha00865.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06542 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06563 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06560 ^ 1)
theorem ha06564 : a06564.IsHomogeneous 45 := by
  unfold a06564
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06563.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06560.pow 1)))

@[irreducible]
def a06565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06562 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06564 ^ 1)
theorem ha06565 : a06565.IsHomogeneous 45 := by
  unfold a06565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06543.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06562.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06564.pow 1)))

@[irreducible]
def a06566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a05994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a03085 ^ 1)
theorem ha06566 : a06566.IsHomogeneous 42 := by
  unfold a06566
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha05994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a06567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06566 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06561 ^ 1)
theorem ha06567 : a06567.IsHomogeneous 42 := by
  unfold a06567
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06547.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06566.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06561.pow 1)))

@[irreducible]
def a06568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06562 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a06567 ^ 1)
theorem ha06568 : a06568.IsHomogeneous 45 := by
  unfold a06568
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06562.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha06567.pow 1)))

@[irreducible]
def a06569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06568 ^ 1)
theorem ha06569 : a06569.IsHomogeneous 45 := by
  unfold a06569
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06565.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06568.pow 1)))

@[irreducible]
def a06570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02008 ^ 1)
theorem ha06570 : a06570.IsHomogeneous 36 := by
  unfold a06570
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06563 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06570 ^ 1)
theorem ha06571 : a06571.IsHomogeneous 45 := by
  unfold a06571
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06563.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06570.pow 1)))

@[irreducible]
def a06572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06554 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06564 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06571 ^ 1)
theorem ha06572 : a06572.IsHomogeneous 45 := by
  unfold a06572
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06564.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06571.pow 1)))

@[irreducible]
def a06573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06565 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06572 ^ 1)
theorem ha06573 : a06573.IsHomogeneous 45 := by
  unfold a06573
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06565.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06572.pow 1)))

@[irreducible]
def a06574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06573 ^ 1)
theorem ha06574 : a06574.IsHomogeneous 45 := by
  unfold a06574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06569.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06573.pow 1)))

@[irreducible]
def a06575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a05839 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06574 ^ 1)
theorem ha06575 : a06575.IsHomogeneous 50 := by
  unfold a06575
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha05839.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06574.pow 1)))

@[irreducible]
def a06576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06575 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06574 ^ 1)
theorem ha06576 : a06576.IsHomogeneous 50 := by
  unfold a06576
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06575.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06574.pow 1)))

@[irreducible]
def a06577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00201 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a00506 ^ 1)
theorem ha06577 : a06577.IsHomogeneous 45 := by
  unfold a06577
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00621.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00201 ^ 1 * a00506 ^ 1)
theorem ha06578 : a06578.IsHomogeneous 39 := by
  unfold a06578
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00621 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00621 ^ 1)
theorem ha06579 : a06579.IsHomogeneous 45 := by
  unfold a06579
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00621.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06577 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06579 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06578 ^ 1)
theorem ha06580 : a06580.IsHomogeneous 45 := by
  unfold a06580
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06577.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06579.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06578.pow 1)))

@[irreducible]
def a06581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00506 ^ 1)
theorem ha06581 : a06581.IsHomogeneous 42 := by
  unfold a06581
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a01327 ^ 1)
theorem ha06582 : a06582.IsHomogeneous 42 := by
  unfold a06582
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06577 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06582 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06581 ^ 1)
theorem ha06583 : a06583.IsHomogeneous 45 := by
  unfold a06583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06582.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06581.pow 1)))

@[irreducible]
def a06584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00506 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1)
theorem ha06584 : a06584.IsHomogeneous 42 := by
  unfold a06584
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a06585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06581 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06584 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06578 ^ 1)
theorem ha06585 : a06585.IsHomogeneous 42 := by
  unfold a06585
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06581.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06584.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06578.pow 1)))

@[irreducible]
def a06586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06583 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06585 ^ 1)
theorem ha06586 : a06586.IsHomogeneous 45 := by
  unfold a06586
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06583.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06585.pow 1)))

@[irreducible]
def a06587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00621 ^ 1)
theorem ha06587 : a06587.IsHomogeneous 33 := by
  unfold a06587
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00201 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00621 ^ 1)
theorem ha06588 : a06588.IsHomogeneous 33 := by
  unfold a06588
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06578 ^ 1)
theorem ha06589 : a06589.IsHomogeneous 39 := by
  unfold a06589
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06587.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06588.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06578.pow 1)))

@[irreducible]
def a06590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01555 ^ 1)
theorem ha06590 : a06590.IsHomogeneous 39 := by
  unfold a06590
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a06591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06579 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06587 ^ 1)
theorem ha06591 : a06591.IsHomogeneous 45 := by
  unfold a06591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06579.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06587.pow 1)))

@[irreducible]
def a06592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06580 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06591 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06589 ^ 1)
theorem ha06592 : a06592.IsHomogeneous 45 := by
  unfold a06592
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06591.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06589.pow 1)))

@[irreducible]
def a06593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha06593 : a06593.IsHomogeneous 36 := by
  unfold a06593
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a06594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06593 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06584 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06588 ^ 1)
theorem ha06594 : a06594.IsHomogeneous 42 := by
  unfold a06594
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06593.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06584.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06588.pow 1)))

@[irreducible]
def a06595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06585 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06594 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06589 ^ 1)
theorem ha06595 : a06595.IsHomogeneous 42 := by
  unfold a06595
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06585.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06594.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06589.pow 1)))

@[irreducible]
def a06596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06592 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06595 ^ 1)
theorem ha06596 : a06596.IsHomogeneous 45 := by
  unfold a06596
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06592.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06595.pow 1)))

@[irreducible]
def a06597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00621 ^ 1 * a01327 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00621 ^ 1)
theorem ha06597 : a06597.IsHomogeneous 45 := by
  unfold a06597
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a01327 ^ 1)
theorem ha06598 : a06598.IsHomogeneous 39 := by
  unfold a06598
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06577 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06597 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06598 ^ 1)
theorem ha06599 : a06599.IsHomogeneous 45 := by
  unfold a06599
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06577.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06597.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06598.pow 1)))

@[irreducible]
def a06600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a01555 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a03330 ^ 1)
theorem ha06600 : a06600.IsHomogeneous 45 := by
  unfold a06600
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01555.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a06601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06600 ^ 1)
theorem ha06601 : a06601.IsHomogeneous 45 := by
  unfold a06601
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06579.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06597.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06600.pow 1)))

@[irreducible]
def a06602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06599 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06601 ^ 1)
theorem ha06602 : a06602.IsHomogeneous 45 := by
  unfold a06602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06599.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06601.pow 1)))

@[irreducible]
def a06603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a02935 ^ 1)
theorem ha06603 : a06603.IsHomogeneous 42 := by
  unfold a06603
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06582 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06603 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06598 ^ 1)
theorem ha06604 : a06604.IsHomogeneous 42 := by
  unfold a06604
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06603.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06598.pow 1)))

@[irreducible]
def a06605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06599 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a06604 ^ 1)
theorem ha06605 : a06605.IsHomogeneous 45 := by
  unfold a06605
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06599.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha06604.pow 1)))

@[irreducible]
def a06606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06605 ^ 1)
theorem ha06606 : a06606.IsHomogeneous 45 := by
  unfold a06606
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06602.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06605.pow 1)))

@[irreducible]
def a06607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a06376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a03330 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1)
theorem ha06607 : a06607.IsHomogeneous 36 := by
  unfold a06607
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a06608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06600 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06607 ^ 1)
theorem ha06608 : a06608.IsHomogeneous 45 := by
  unfold a06608
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06600.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06607.pow 1)))

@[irreducible]
def a06609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06591 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06601 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06608 ^ 1)
theorem ha06609 : a06609.IsHomogeneous 45 := by
  unfold a06609
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06591.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06601.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06608.pow 1)))

@[irreducible]
def a06610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06592 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06602 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06609 ^ 1)
theorem ha06610 : a06610.IsHomogeneous 45 := by
  unfold a06610
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06592.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06602.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06609.pow 1)))

@[irreducible]
def a06611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06610 ^ 1)
theorem ha06611 : a06611.IsHomogeneous 45 := by
  unfold a06611
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06606.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06610.pow 1)))

@[irreducible]
def a06612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06611 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a05839 ^ 1)
theorem ha06612 : a06612.IsHomogeneous 50 := by
  unfold a06612
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06611.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha05839.pow 1)))

@[irreducible]
def a06613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06612 ^ 1)
theorem ha06613 : a06613.IsHomogeneous 50 := by
  unfold a06613
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06612.pow 1)))

@[irreducible]
def a06614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06613 ^ 1)
theorem ha06614 : a06614.IsHomogeneous 50 := by
  unfold a06614
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06613.pow 1)))

@[irreducible]
def a06615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06611 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06612 ^ 1)
theorem ha06615 : a06615.IsHomogeneous 50 := by
  unfold a06615
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06611.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06612.pow 1)))

@[irreducible]
def a06616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06615 ^ 1)
theorem ha06616 : a06616.IsHomogeneous 50 := by
  unfold a06616
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06615.pow 1)))

@[irreducible]
def a06617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06616 ^ 1)
theorem ha06617 : a06617.IsHomogeneous 50 := by
  unfold a06617
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06616.pow 1)))

@[irreducible]
def a06618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1)
theorem ha06618 : a06618.IsHomogeneous 45 := by
  unfold a06618
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a06619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha06619 : a06619.IsHomogeneous 39 := by
  unfold a06619
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00317 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha06620 : a06620.IsHomogeneous 45 := by
  unfold a06620
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a06621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06618 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06619 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06620 ^ 1)
theorem ha06621 : a06621.IsHomogeneous 45 := by
  unfold a06621
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06618.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06619.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06620.pow 1)))

@[irreducible]
def a06622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00555 ^ 1)
theorem ha06622 : a06622.IsHomogeneous 42 := by
  unfold a06622
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00171 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1)
theorem ha06623 : a06623.IsHomogeneous 42 := by
  unfold a06623
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a06624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06618 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06622 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06623 ^ 1)
theorem ha06624 : a06624.IsHomogeneous 45 := by
  unfold a06624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06618.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06622.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06623.pow 1)))

@[irreducible]
def a06625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha06625 : a06625.IsHomogeneous 42 := by
  unfold a06625
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a06626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06622 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06625 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a06619 ^ 1)
theorem ha06626 : a06626.IsHomogeneous 42 := by
  unfold a06626
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06625.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha06619.pow 1)))

@[irreducible]
def a06627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06624 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06626 ^ 1)
theorem ha06627 : a06627.IsHomogeneous 45 := by
  unfold a06627
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06621.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06624.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06626.pow 1)))

@[irreducible]
def a06628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00171 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1)
theorem ha06628 : a06628.IsHomogeneous 39 := by
  unfold a06628
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00171.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00171 ^ 1)
theorem ha06629 : a06629.IsHomogeneous 33 := by
  unfold a06629
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a06630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06628 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06618 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06629 ^ 1)
theorem ha06630 : a06630.IsHomogeneous 45 := by
  unfold a06630
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06618.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06629.pow 1)))

@[irreducible]
def a06631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00865 ^ 1)
theorem ha06631 : a06631.IsHomogeneous 39 := by
  unfold a06631
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06628 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06631 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06620 ^ 1)
theorem ha06632 : a06632.IsHomogeneous 45 := by
  unfold a06632
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06628.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06631.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06620.pow 1)))

@[irreducible]
def a06633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06621 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06630 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06632 ^ 1)
theorem ha06633 : a06633.IsHomogeneous 45 := by
  unfold a06633
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06621.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06630.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06632.pow 1)))

@[irreducible]
def a06634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00171 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1)
theorem ha06634 : a06634.IsHomogeneous 36 := by
  unfold a06634
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06634 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06623 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06629 ^ 1)
theorem ha06635 : a06635.IsHomogeneous 42 := by
  unfold a06635
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06623.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06629.pow 1)))

@[irreducible]
def a06636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06624 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06630 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a06635 ^ 1)
theorem ha06636 : a06636.IsHomogeneous 45 := by
  unfold a06636
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06624.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06630.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha06635.pow 1)))

@[irreducible]
def a06637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06636 ^ 1)
theorem ha06637 : a06637.IsHomogeneous 45 := by
  unfold a06637
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06633.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06636.pow 1)))

@[irreducible]
def a06638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00317 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a00555 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00555 ^ 1 * a00865 ^ 1)
theorem ha06638 : a06638.IsHomogeneous 39 := by
  unfold a06638
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00129 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00032 ^ 1 * a00317 ^ 1 * a01429 ^ 1)
theorem ha06639 : a06639.IsHomogeneous 39 := by
  unfold a06639
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a06640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06619 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06639 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06638 ^ 1)
theorem ha06640 : a06640.IsHomogeneous 39 := by
  unfold a06640
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06639.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06638.pow 1)))

@[irreducible]
def a06641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a00865 ^ 1)
theorem ha06641 : a06641.IsHomogeneous 45 := by
  unfold a06641
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06641 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06638 ^ 1)
theorem ha06642 : a06642.IsHomogeneous 45 := by
  unfold a06642
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06641.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06638.pow 1)))

@[irreducible]
def a06643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06621 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06640 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06642 ^ 1)
theorem ha06643 : a06643.IsHomogeneous 45 := by
  unfold a06643
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06640.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06642.pow 1)))

@[irreducible]
def a06644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a06044 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1 * a03116 ^ 1)
theorem ha06644 : a06644.IsHomogeneous 42 := by
  unfold a06644
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha06044.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a06645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06625 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06644 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06639 ^ 1)
theorem ha06645 : a06645.IsHomogeneous 42 := by
  unfold a06645
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06625.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06644.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06639.pow 1)))

@[irreducible]
def a06646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06626 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06645 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a06640 ^ 1)
theorem ha06646 : a06646.IsHomogeneous 42 := by
  unfold a06646
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06645.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha06640.pow 1)))

@[irreducible]
def a06647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06643 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06646 ^ 1)
theorem ha06647 : a06647.IsHomogeneous 45 := by
  unfold a06647
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06643.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06646.pow 1)))

@[irreducible]
def a06648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02008 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a02008 ^ 1)
theorem ha06648 : a06648.IsHomogeneous 36 := by
  unfold a06648
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha04086.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06631 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06648 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06641 ^ 1)
theorem ha06649 : a06649.IsHomogeneous 45 := by
  unfold a06649
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06631.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06648.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06641.pow 1)))

@[irreducible]
def a06650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06649 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06642 ^ 1)
theorem ha06650 : a06650.IsHomogeneous 45 := by
  unfold a06650
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06649.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06642.pow 1)))

@[irreducible]
def a06651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06643 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06650 ^ 1)
theorem ha06651 : a06651.IsHomogeneous 45 := by
  unfold a06651
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06633.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06643.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06650.pow 1)))

@[irreducible]
def a06652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06647 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06651 ^ 1)
theorem ha06652 : a06652.IsHomogeneous 45 := by
  unfold a06652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06637.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06647.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06651.pow 1)))

@[irreducible]
def a06653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00207 ^ 1 * a01327 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00506 ^ 1)
theorem ha06653 : a06653.IsHomogeneous 30 := by
  unfold a06653
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1)
theorem ha06654 : a06654.IsHomogeneous 30 := by
  unfold a06654
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a06655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a01575 ^ 1)
theorem ha06655 : a06655.IsHomogeneous 30 := by
  unfold a06655
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01575.pow 1)))

end CycleQ2Concrete
