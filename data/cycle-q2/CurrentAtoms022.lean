import Proposal.CurrentAtoms021

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a07424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07421 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07423 ^ 1)
theorem ha07424 : a07424.IsHomogeneous 57 := by
  unfold a07424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07423.pow 1)))

@[irreducible]
def a07425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07421 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07424 ^ 1)
theorem ha07425 : a07425.IsHomogeneous 57 := by
  unfold a07425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07424.pow 1)))

@[irreducible]
def a07426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a04004 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a07425 ^ 1)
theorem ha07426 : a07426.IsHomogeneous 75 := by
  unfold a07426
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha04004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha07425.pow 1)))

@[irreducible]
def a07427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07426 ^ 1)
theorem ha07427 : a07427.IsHomogeneous 75 := by
  unfold a07427
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07413.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07426.pow 1)))

@[irreducible]
def a07428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07427 ^ 1)
theorem ha07428 : a07428.IsHomogeneous 75 := by
  unfold a07428
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07414.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07427.pow 1)))

@[irreducible]
def a07429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07415 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07428 ^ 1)
theorem ha07429 : a07429.IsHomogeneous 75 := by
  unfold a07429
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07428.pow 1)))

@[irreducible]
def a07430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07429 ^ 1)
theorem ha07430 : a07430.IsHomogeneous 75 := by
  unfold a07430
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07429.pow 1)))

@[irreducible]
def a07431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04008 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07430 ^ 1)
theorem ha07431 : a07431.IsHomogeneous 81 := by
  unfold a07431
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07430.pow 1)))

@[irreducible]
def a07432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07407 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07431 ^ 1)
theorem ha07432 : a07432.IsHomogeneous 87 := by
  unfold a07432
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07407.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07431.pow 1)))

@[irreducible]
def a07433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07408 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07432 ^ 1)
theorem ha07433 : a07433.IsHomogeneous 93 := by
  unfold a07433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07408.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07432.pow 1)))

@[irreducible]
def a07434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07409 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07433 ^ 1)
theorem ha07434 : a07434.IsHomogeneous 99 := by
  unfold a07434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07409.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07433.pow 1)))

@[irreducible]
def a07435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a07120 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00308 ^ 1 * a03803 ^ 1)
theorem ha07435 : a07435.IsHomogeneous 72 := by
  unfold a07435
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07120.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00308.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a07436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07435 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07405 ^ 1)
theorem ha07436 : a07436.IsHomogeneous 102 := by
  unfold a07436
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07435.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07405.pow 1)))

@[irreducible]
def a07437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07436 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07406 ^ 1)
theorem ha07437 : a07437.IsHomogeneous 102 := by
  unfold a07437
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07436.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07406.pow 1)))

@[irreducible]
def a07438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07437 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07409 ^ 1)
theorem ha07438 : a07438.IsHomogeneous 102 := by
  unfold a07438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07437.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07409.pow 1)))

@[irreducible]
def a07439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07438 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07434 ^ 1)
theorem ha07439 : a07439.IsHomogeneous 105 := by
  unfold a07439
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07438.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07434.pow 1)))

@[irreducible]
def a07440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04015 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a07439 ^ 1)
theorem ha07440 : a07440.IsHomogeneous 141 := by
  unfold a07440
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04015.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha07439.pow 1)))

@[irreducible]
def a07441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07399 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a07440 ^ 1)
theorem ha07441 : a07441.IsHomogeneous 177 := by
  unfold a07441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07399.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha07440.pow 1)))

@[irreducible]
def a07442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07400 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07441 ^ 1)
theorem ha07442 : a07442.IsHomogeneous 216 := by
  unfold a07442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07400.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07441.pow 1)))

@[irreducible]
def a07443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07403 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a07442 ^ 1)
theorem ha07443 : a07443.IsHomogeneous 252 := by
  unfold a07443
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07403.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha07442.pow 1)))

@[irreducible]
def a07444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01938 ^ 1 * a01974 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a03963 ^ 1)
theorem ha07444 : a07444.IsHomogeneous 171 := by
  unfold a07444
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01938.pow 1)).mul (ha01974.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a07445 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1 * a01974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a04025 ^ 1)
theorem ha07445 : a07445.IsHomogeneous 210 := by
  unfold a07445
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).mul (ha01974.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha04025.pow 1)))

@[irreducible]
def a07446 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07444 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07445 ^ 1)
theorem ha07446 : a07446.IsHomogeneous 210 := by
  unfold a07446
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07445.pow 1)))

@[irreducible]
def a07447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a07363 ^ 1)
theorem ha07447 : a07447.IsHomogeneous 135 := by
  unfold a07447
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a07448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07444 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a07447 ^ 1)
theorem ha07448 : a07448.IsHomogeneous 171 := by
  unfold a07448
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07444.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha07447.pow 1)))

@[irreducible]
def a07449 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07448 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07446 ^ 1)
theorem ha07449 : a07449.IsHomogeneous 210 := by
  unfold a07449
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07448.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07446.pow 1)))

@[irreducible]
def a07450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01938 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a03963 ^ 1)
theorem ha07450 : a07450.IsHomogeneous 129 := by
  unfold a07450
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a07451 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00260 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a04023 ^ 1)
theorem ha07451 : a07451.IsHomogeneous 168 := by
  unfold a07451
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha04023.pow 1)))

@[irreducible]
def a07452 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07451 ^ 1)
theorem ha07452 : a07452.IsHomogeneous 168 := by
  unfold a07452
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07450.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07451.pow 1)))

@[irreducible]
def a07453 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00829 ^ 1)
theorem ha07453 : a07453.IsHomogeneous 126 := by
  unfold a07453
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a07454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (10 : ℂ)) * a00829 ^ 1)
theorem ha07454 : a07454.IsHomogeneous 84 := by
  unfold a07454
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a07455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a07454 ^ 1)
theorem ha07455 : a07455.IsHomogeneous 84 := by
  unfold a07455
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha07454.pow 1)))

@[irreducible]
def a07456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07453 ^ 1)
theorem ha07456 : a07456.IsHomogeneous 126 := by
  unfold a07456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07453.pow 1)))

@[irreducible]
def a07457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a04023 ^ 1)
theorem ha07457 : a07457.IsHomogeneous 168 := by
  unfold a07457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07456.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha04023.pow 1)))

@[irreducible]
def a07458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07457 ^ 1)
theorem ha07458 : a07458.IsHomogeneous 168 := by
  unfold a07458
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07457.pow 1)))

@[irreducible]
def a07459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07458 ^ 1)
theorem ha07459 : a07459.IsHomogeneous 168 := by
  unfold a07459
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07452.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07458.pow 1)))

@[irreducible]
def a07460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07459 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00829 ^ 1 * a04025 ^ 1)
theorem ha07460 : a07460.IsHomogeneous 210 := by
  unfold a07460
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00829.pow 1)).mul (ha04025.pow 1)))

@[irreducible]
def a07461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07445 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a07460 ^ 1)
theorem ha07461 : a07461.IsHomogeneous 210 := by
  unfold a07461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha07460.pow 1)))

@[irreducible]
def a07462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07446 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07461 ^ 1)
theorem ha07462 : a07462.IsHomogeneous 210 := by
  unfold a07462
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07446.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07461.pow 1)))

@[irreducible]
def a07463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07462 ^ 1)
theorem ha07463 : a07463.IsHomogeneous 210 := by
  unfold a07463
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07449.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07462.pow 1)))

@[irreducible]
def a07464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a07463 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00309 ^ 1 * a04028 ^ 1)
theorem ha07464 : a07464.IsHomogeneous 258 := by
  unfold a07464
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07463.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00309.pow 1)).mul (ha04028.pow 1)))

@[irreducible]
def a07465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07464 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a07401 ^ 1)
theorem ha07465 : a07465.IsHomogeneous 288 := by
  unfold a07465
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07464.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha07401.pow 1)))

@[irreducible]
def a07466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07465 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a07402 ^ 1)
theorem ha07466 : a07466.IsHomogeneous 288 := by
  unfold a07466
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07465.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha07402.pow 1)))

@[irreducible]
def a07467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07466 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a07403 ^ 1)
theorem ha07467 : a07467.IsHomogeneous 288 := by
  unfold a07467
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07466.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha07403.pow 1)))

@[irreducible]
def a07468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07467 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a07443 ^ 1)
theorem ha07468 : a07468.IsHomogeneous 288 := by
  unfold a07468
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07467.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha07443.pow 1)))

@[irreducible]
def a07469 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a07468 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a04032 ^ 1)
theorem ha07469 : a07469.IsHomogeneous 714 := by
  unfold a07469
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha07468.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a07470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07391 ^ 1)
theorem ha07470 : a07470.IsHomogeneous 1047 := by
  unfold a07470
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07391.pow 1)))

@[irreducible]
def a07471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07392 ^ 1)
theorem ha07471 : a07471.IsHomogeneous 1380 := by
  unfold a07471
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07392.pow 1)))

@[irreducible]
def a07472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07471 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07393 ^ 1)
theorem ha07472 : a07472.IsHomogeneous 1713 := by
  unfold a07472
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07471.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07393.pow 1)))

@[irreducible]
def a07473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07472 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07397 ^ 1)
theorem ha07473 : a07473.IsHomogeneous 2046 := by
  unfold a07473
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07397.pow 1)))

@[irreducible]
def a07474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07387 ^ 1) + (C ((32 : ℂ) / (243 : ℂ)) * a00042 ^ 5 * a07473 ^ 1)
theorem ha07474 : a07474.IsHomogeneous 2166 := by
  unfold a07474
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (243 : ℂ))).mul (ha00042.pow 5)).mul (ha07473.pow 1)))

@[irreducible]
def a07475 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a04037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07474 ^ 1)
theorem ha07475 : a07475.IsHomogeneous 2226 := by
  unfold a07475
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha04037.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07474.pow 1)))

@[irreducible]
def a07476 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07475 ^ 1)
theorem ha07476 : a07476.IsHomogeneous 2286 := by
  unfold a07476
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07475.pow 1)))

@[irreducible]
def a07477 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07476 ^ 1)
theorem ha07477 : a07477.IsHomogeneous 2346 := by
  unfold a07477
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05707.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07476.pow 1)))

@[irreducible]
def a07478 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07477 ^ 1)
theorem ha07478 : a07478.IsHomogeneous 2406 := by
  unfold a07478
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07477.pow 1)))

@[irreducible]
def a07479 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a01986 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a04045 ^ 1)
theorem ha07479 : a07479.IsHomogeneous 450 := by
  unfold a07479
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha01986.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha04045.pow 1)))

@[irreducible]
def a07480 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01986 ^ 1 * a02041 ^ 1)
theorem ha07480 : a07480.IsHomogeneous 390 := by
  unfold a07480
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01986.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a07481 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a07480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07479 ^ 1)
theorem ha07481 : a07481.IsHomogeneous 450 := by
  unfold a07481
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha07480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07479.pow 1)))

@[irreducible]
def a07482 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a04043 ^ 1)
theorem ha07482 : a07482.IsHomogeneous 348 := by
  unfold a07482
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha04043.pow 1)))

@[irreducible]
def a07483 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a02041 ^ 1)
theorem ha07483 : a07483.IsHomogeneous 288 := by
  unfold a07483
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a07484 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a07483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07482 ^ 1)
theorem ha07484 : a07484.IsHomogeneous 348 := by
  unfold a07484
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha07483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07482.pow 1)))

@[irreducible]
def a07485 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00880 ^ 1)
theorem ha07485 : a07485.IsHomogeneous 246 := by
  unfold a07485
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a07486 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 2)
theorem ha07486 : a07486.IsHomogeneous 204 := by
  unfold a07486
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 2)))

@[irreducible]
def a07487 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07486 ^ 1)
theorem ha07487 : a07487.IsHomogeneous 204 := by
  unfold a07487
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07486.pow 1)))

@[irreducible]
def a07488 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07487 ^ 1)
theorem ha07488 : a07488.IsHomogeneous 306 := by
  unfold a07488
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07485.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07487.pow 1)))

@[irreducible]
def a07489 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a04043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07488 ^ 1)
theorem ha07489 : a07489.IsHomogeneous 408 := by
  unfold a07489
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha04043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07488.pow 1)))

@[irreducible]
def a07490 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07482 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07489 ^ 1)
theorem ha07490 : a07490.IsHomogeneous 408 := by
  unfold a07490
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07482.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07489.pow 1)))

@[irreducible]
def a07491 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07490 ^ 1)
theorem ha07491 : a07491.IsHomogeneous 408 := by
  unfold a07491
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07490.pow 1)))

@[irreducible]
def a07492 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a04045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07491 ^ 1)
theorem ha07492 : a07492.IsHomogeneous 510 := by
  unfold a07492
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha04045.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07491.pow 1)))

@[irreducible]
def a07493 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07492 ^ 1)
theorem ha07493 : a07493.IsHomogeneous 510 := by
  unfold a07493
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07492.pow 1)))

@[irreducible]
def a07494 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07493 ^ 1)
theorem ha07494 : a07494.IsHomogeneous 510 := by
  unfold a07494
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07493.pow 1)))

@[irreducible]
def a07495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00876 ^ 1 * a02038 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00878 ^ 1 * a02032 ^ 1)
theorem ha07495 : a07495.IsHomogeneous 183 := by
  unfold a07495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00876.pow 1)).mul (ha02038.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00878.pow 1)).mul (ha02032.pow 1)))

@[irreducible]
def a07496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02032 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a04131 ^ 1)
theorem ha07496 : a07496.IsHomogeneous 141 := by
  unfold a07496
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02032.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04131.pow 1)))

@[irreducible]
def a07497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07495 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07496 ^ 1)
theorem ha07497 : a07497.IsHomogeneous 183 := by
  unfold a07497
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07495.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07496.pow 1)))

@[irreducible]
def a07498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00326 ^ 1 * a04144 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00876 ^ 1 * a02038 ^ 1)
theorem ha07498 : a07498.IsHomogeneous 225 := by
  unfold a07498
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00326.pow 1)).mul (ha04144.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00876.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a07499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07498 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07495 ^ 1)
theorem ha07499 : a07499.IsHomogeneous 225 := by
  unfold a07499
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07498.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07495.pow 1)))

@[irreducible]
def a07500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07499 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07497 ^ 1)
theorem ha07500 : a07500.IsHomogeneous 225 := by
  unfold a07500
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07499.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07497.pow 1)))

@[irreducible]
def a07501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a00809 ^ 1)
theorem ha07501 : a07501.IsHomogeneous 51 := by
  unfold a07501
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a00809 ^ 1)
theorem ha07502 : a07502.IsHomogeneous 48 := by
  unfold a07502
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha07503 : a07503.IsHomogeneous 51 := by
  unfold a07503
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07501 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a07503 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a07502 ^ 1)
theorem ha07504 : a07504.IsHomogeneous 51 := by
  unfold a07504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07501.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha07503.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha07502.pow 1)))

@[irreducible]
def a07505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha07505 : a07505.IsHomogeneous 51 := by
  unfold a07505
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a02008 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha07506 : a07506.IsHomogeneous 51 := by
  unfold a07506
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07501 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07505 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a07506 ^ 1)
theorem ha07507 : a07507.IsHomogeneous 51 := by
  unfold a07507
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07501.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07505.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha07506.pow 1)))

@[irreducible]
def a07508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha07508 : a07508.IsHomogeneous 51 := by
  unfold a07508
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a07509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07503 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a07508 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a07505 ^ 1)
theorem ha07509 : a07509.IsHomogeneous 51 := by
  unfold a07509
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha07508.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha07505.pow 1)))

@[irreducible]
def a07510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07507 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a07509 ^ 1)
theorem ha07510 : a07510.IsHomogeneous 51 := by
  unfold a07510
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07507.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha07509.pow 1)))

@[irreducible]
def a07511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha07511 : a07511.IsHomogeneous 51 := by
  unfold a07511
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a03890 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01896 ^ 1)
theorem ha07512 : a07512.IsHomogeneous 51 := by
  unfold a07512
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a07513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07511 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a07512 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07502 ^ 1)
theorem ha07513 : a07513.IsHomogeneous 51 := by
  unfold a07513
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07511.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha07512.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07502.pow 1)))

@[irreducible]
def a07514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00809 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00298 ^ 1)
theorem ha07514 : a07514.IsHomogeneous 54 := by
  unfold a07514
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00809.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a07515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07514 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07511 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07503 ^ 1)
theorem ha07515 : a07515.IsHomogeneous 54 := by
  unfold a07515
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07514.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07511.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07503.pow 1)))

@[irreducible]
def a07516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07515 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07513 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07504 ^ 1)
theorem ha07516 : a07516.IsHomogeneous 54 := by
  unfold a07516
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07515.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07513.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07504.pow 1)))

@[irreducible]
def a07517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha07517 : a07517.IsHomogeneous 54 := by
  unfold a07517
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a07518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07514 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a07517 ^ 1)
theorem ha07518 : a07518.IsHomogeneous 54 := by
  unfold a07518
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07514.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha07517.pow 1)))

@[irreducible]
def a07519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07515 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07518 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07509 ^ 1)
theorem ha07519 : a07519.IsHomogeneous 54 := by
  unfold a07519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07515.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07518.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07509.pow 1)))

@[irreducible]
def a07520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07519 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07510 ^ 1)
theorem ha07520 : a07520.IsHomogeneous 54 := by
  unfold a07520
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07519.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07510.pow 1)))

@[irreducible]
def a07521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01896 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a00865 ^ 1)
theorem ha07521 : a07521.IsHomogeneous 48 := by
  unfold a07521
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00298 ^ 1 * a02008 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a00865 ^ 1)
theorem ha07522 : a07522.IsHomogeneous 51 := by
  unfold a07522
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00298.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07522 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07521 ^ 1)
theorem ha07523 : a07523.IsHomogeneous 51 := by
  unfold a07523
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07501.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07522.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07521.pow 1)))

@[irreducible]
def a07524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00129 ^ 1 * a03890 ^ 1)
theorem ha07524 : a07524.IsHomogeneous 48 := by
  unfold a07524
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00129.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07502 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a07521 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a07524 ^ 1)
theorem ha07525 : a07525.IsHomogeneous 48 := by
  unfold a07525
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07502.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha07521.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha07524.pow 1)))

@[irreducible]
def a07526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07523 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a07525 ^ 1)
theorem ha07526 : a07526.IsHomogeneous 51 := by
  unfold a07526
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07523.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha07525.pow 1)))

@[irreducible]
def a07527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a04086 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a02008 ^ 1)
theorem ha07527 : a07527.IsHomogeneous 48 := by
  unfold a07527
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha04086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07506 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a07527 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a07522 ^ 1)
theorem ha07528 : a07528.IsHomogeneous 51 := by
  unfold a07528
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha07527.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha07522.pow 1)))

@[irreducible]
def a07529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07523 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a07528 ^ 1)
theorem ha07529 : a07529.IsHomogeneous 51 := by
  unfold a07529
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07523.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha07528.pow 1)))

@[irreducible]
def a07530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07529 ^ 1)
theorem ha07530 : a07530.IsHomogeneous 51 := by
  unfold a07530
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07526.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07529.pow 1)))

@[irreducible]
def a07531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03890 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a07248 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03890 ^ 1)
theorem ha07531 : a07531.IsHomogeneous 51 := by
  unfold a07531
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha07248.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07512 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a07531 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07524 ^ 1)
theorem ha07532 : a07532.IsHomogeneous 51 := by
  unfold a07532
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07512.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha07531.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07524.pow 1)))

@[irreducible]
def a07533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07513 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a07532 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07525 ^ 1)
theorem ha07533 : a07533.IsHomogeneous 51 := by
  unfold a07533
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha07532.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07525.pow 1)))

@[irreducible]
def a07534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07516 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07533 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07526 ^ 1)
theorem ha07534 : a07534.IsHomogeneous 54 := by
  unfold a07534
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07516.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07533.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07526.pow 1)))

@[irreducible]
def a07535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07534 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07530 ^ 1)
theorem ha07535 : a07535.IsHomogeneous 54 := by
  unfold a07535
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07534.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07530.pow 1)))

@[irreducible]
def a07536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01617 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a02008 ^ 1)
theorem ha07536 : a07536.IsHomogeneous 54 := by
  unfold a07536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01617.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03432 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01617 ^ 1)
theorem ha07537 : a07537.IsHomogeneous 54 := by
  unfold a07537
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a07538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07536 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07537 ^ 1)
theorem ha07538 : a07538.IsHomogeneous 54 := by
  unfold a07538
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07536.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07537.pow 1)))

@[irreducible]
def a07539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a02008 ^ 1)
theorem ha07539 : a07539.IsHomogeneous 54 := by
  unfold a07539
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07536 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a07539 ^ 1)
theorem ha07540 : a07540.IsHomogeneous 54 := by
  unfold a07540
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07536.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha07539.pow 1)))

@[irreducible]
def a07541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07538 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07540 ^ 1)
theorem ha07541 : a07541.IsHomogeneous 54 := by
  unfold a07541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07540.pow 1)))

@[irreducible]
def a07542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03432 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a06529 ^ 1)
theorem ha07542 : a07542.IsHomogeneous 54 := by
  unfold a07542
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03432.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha06529.pow 1)))

@[irreducible]
def a07543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07542 ^ 1)
theorem ha07543 : a07543.IsHomogeneous 54 := by
  unfold a07543
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07542.pow 1)))

@[irreducible]
def a07544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07538 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07543 ^ 1)
theorem ha07544 : a07544.IsHomogeneous 54 := by
  unfold a07544
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07543.pow 1)))

@[irreducible]
def a07545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07544 ^ 1)
theorem ha07545 : a07545.IsHomogeneous 54 := by
  unfold a07545
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07544.pow 1)))

@[irreducible]
def a07546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a01324 ^ 1)
theorem ha07546 : a07546.IsHomogeneous 6 := by
  unfold a07546
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha01324.pow 1)))

@[irreducible]
def a07547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a02931 ^ 1)
theorem ha07547 : a07547.IsHomogeneous 6 := by
  unfold a07547
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha02931.pow 1)))

@[irreducible]
def a07548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07546 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a07547 ^ 1)
theorem ha07548 : a07548.IsHomogeneous 6 := by
  unfold a07548
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha07547.pow 1)))

@[irreducible]
def a07549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00505 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a07546 ^ 1)
theorem ha07549 : a07549.IsHomogeneous 6 := by
  unfold a07549
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00505.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha07546.pow 1)))

@[irreducible]
def a07550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07548 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a07549 ^ 1)
theorem ha07550 : a07550.IsHomogeneous 6 := by
  unfold a07550
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha07549.pow 1)))

@[irreducible]
def a07551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a05749 ^ 1)
theorem ha07551 : a07551.IsHomogeneous 6 := by
  unfold a07551
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha05749.pow 1)))

@[irreducible]
def a07552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07547 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07551 ^ 1)
theorem ha07552 : a07552.IsHomogeneous 6 := by
  unfold a07552
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07547.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07551.pow 1)))

@[irreducible]
def a07553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07548 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a07552 ^ 1)
theorem ha07553 : a07553.IsHomogeneous 6 := by
  unfold a07553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha07552.pow 1)))

@[irreducible]
def a07554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07553 ^ 1)
theorem ha07554 : a07554.IsHomogeneous 6 := by
  unfold a07554
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07553.pow 1)))

@[irreducible]
def a07555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha07555 : a07555.IsHomogeneous 12 := by
  unfold a07555
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a07556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07550 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a07555 ^ 1)
theorem ha07556 : a07556.IsHomogeneous 12 := by
  unfold a07556
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha07555.pow 1)))

@[irreducible]
def a07557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07554 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07556 ^ 1)
theorem ha07557 : a07557.IsHomogeneous 12 := by
  unfold a07557
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07556.pow 1)))

@[irreducible]
def a07558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a07557 ^ 1) + (C ((7 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3)
theorem ha07558 : a07558.IsHomogeneous 18 := by
  unfold a07558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha07557.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a07559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a07558 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00218 ^ 1 * a04086 ^ 1)
theorem ha07559 : a07559.IsHomogeneous 54 := by
  unfold a07559
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00218.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a07560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07539 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a07559 ^ 1)
theorem ha07560 : a07560.IsHomogeneous 54 := by
  unfold a07560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha07559.pow 1)))

@[irreducible]
def a07561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07540 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a07560 ^ 1)
theorem ha07561 : a07561.IsHomogeneous 54 := by
  unfold a07561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha07560.pow 1)))

@[irreducible]
def a07562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07561 ^ 1)
theorem ha07562 : a07562.IsHomogeneous 54 := by
  unfold a07562
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07561.pow 1)))

@[irreducible]
def a07563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07562 ^ 1)
theorem ha07563 : a07563.IsHomogeneous 54 := by
  unfold a07563
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07562.pow 1)))

@[irreducible]
def a07564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00201 ^ 1 * a00865 ^ 1)
theorem ha07564 : a07564.IsHomogeneous 48 := by
  unfold a07564
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00201.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00129 ^ 1 * a01555 ^ 1)
theorem ha07565 : a07565.IsHomogeneous 48 := by
  unfold a07565
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00129.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a07566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a00621 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00201 ^ 1 * a00317 ^ 1)
theorem ha07566 : a07566.IsHomogeneous 48 := by
  unfold a07566
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07564 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07565 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a07566 ^ 1)
theorem ha07567 : a07567.IsHomogeneous 48 := by
  unfold a07567
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07564.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07565.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha07566.pow 1)))

@[irreducible]
def a07568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a00865 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00621 ^ 1)
theorem ha07568 : a07568.IsHomogeneous 54 := by
  unfold a07568
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a07569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a00865 ^ 1)
theorem ha07569 : a07569.IsHomogeneous 54 := by
  unfold a07569
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07568 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07569 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a07564 ^ 1)
theorem ha07570 : a07570.IsHomogeneous 54 := by
  unfold a07570
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07569.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha07564.pow 1)))

@[irreducible]
def a07571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01555 ^ 1)
theorem ha07571 : a07571.IsHomogeneous 54 := by
  unfold a07571
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a07572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07568 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07571 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a07565 ^ 1)
theorem ha07572 : a07572.IsHomogeneous 54 := by
  unfold a07572
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07571.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha07565.pow 1)))

@[irreducible]
def a07573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07570 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07572 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a07567 ^ 1)
theorem ha07573 : a07573.IsHomogeneous 54 := by
  unfold a07573
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07572.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha07567.pow 1)))

@[irreducible]
def a07574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00317 ^ 1)
theorem ha07574 : a07574.IsHomogeneous 51 := by
  unfold a07574
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a02008 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00865 ^ 1)
theorem ha07575 : a07575.IsHomogeneous 51 := by
  unfold a07575
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07575 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07564 ^ 1)
theorem ha07576 : a07576.IsHomogeneous 51 := by
  unfold a07576
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07575.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07564.pow 1)))

@[irreducible]
def a07577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha07577 : a07577.IsHomogeneous 51 := by
  unfold a07577
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a07578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07574 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a07577 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a07566 ^ 1)
theorem ha07578 : a07578.IsHomogeneous 51 := by
  unfold a07578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha07577.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha07566.pow 1)))

@[irreducible]
def a07579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07578 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07567 ^ 1)
theorem ha07579 : a07579.IsHomogeneous 51 := by
  unfold a07579
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07578.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07567.pow 1)))

@[irreducible]
def a07580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a02008 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a02008 ^ 1)
theorem ha07580 : a07580.IsHomogeneous 54 := by
  unfold a07580
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07569 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a07580 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a07575 ^ 1)
theorem ha07581 : a07581.IsHomogeneous 54 := by
  unfold a07581
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07569.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha07580.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha07575.pow 1)))

@[irreducible]
def a07582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07570 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07581 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a07576 ^ 1)
theorem ha07582 : a07582.IsHomogeneous 54 := by
  unfold a07582
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07581.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha07576.pow 1)))

@[irreducible]
def a07583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07573 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07582 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a07579 ^ 1)
theorem ha07583 : a07583.IsHomogeneous 54 := by
  unfold a07583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07582.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha07579.pow 1)))

@[irreducible]
def a07584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a01555 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00621 ^ 1)
theorem ha07584 : a07584.IsHomogeneous 51 := by
  unfold a07584
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a07585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a03330 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01555 ^ 1)
theorem ha07585 : a07585.IsHomogeneous 51 := by
  unfold a07585
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a07586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07584 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07585 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07565 ^ 1)
theorem ha07586 : a07586.IsHomogeneous 51 := by
  unfold a07586
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07585.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07565.pow 1)))

@[irreducible]
def a07587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha07587 : a07587.IsHomogeneous 51 := by
  unfold a07587
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a07588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07584 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a07587 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a07566 ^ 1)
theorem ha07588 : a07588.IsHomogeneous 51 := by
  unfold a07588
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha07587.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha07566.pow 1)))

@[irreducible]
def a07589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07588 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07567 ^ 1)
theorem ha07589 : a07589.IsHomogeneous 51 := by
  unfold a07589
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07588.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07567.pow 1)))

@[irreducible]
def a07590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a03330 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a03330 ^ 1)
theorem ha07590 : a07590.IsHomogeneous 54 := by
  unfold a07590
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha03330.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a07591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07571 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a07590 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a07585 ^ 1)
theorem ha07591 : a07591.IsHomogeneous 54 := by
  unfold a07591
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07571.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha07590.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha07585.pow 1)))

@[irreducible]
def a07592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07591 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a07586 ^ 1)
theorem ha07592 : a07592.IsHomogeneous 54 := by
  unfold a07592
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07591.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha07586.pow 1)))

@[irreducible]
def a07593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07573 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07592 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a07589 ^ 1)
theorem ha07593 : a07593.IsHomogeneous 54 := by
  unfold a07593
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07592.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha07589.pow 1)))

@[irreducible]
def a07594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00201 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00129 ^ 1)
theorem ha07594 : a07594.IsHomogeneous 54 := by
  unfold a07594
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a07595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07594 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07577 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07587 ^ 1)
theorem ha07595 : a07595.IsHomogeneous 54 := by
  unfold a07595
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07594.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07577.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07587.pow 1)))

@[irreducible]
def a07596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07595 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07578 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07588 ^ 1)
theorem ha07596 : a07596.IsHomogeneous 54 := by
  unfold a07596
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07578.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07588.pow 1)))

@[irreducible]
def a07597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07596 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07579 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07589 ^ 1)
theorem ha07597 : a07597.IsHomogeneous 54 := by
  unfold a07597
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07596.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07579.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07589.pow 1)))

@[irreducible]
def a07598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07593 ^ 1) + (C ((7 : ℂ) / (90 : ℂ)) * a07597 ^ 1)
theorem ha07598 : a07598.IsHomogeneous 54 := by
  unfold a07598
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07593.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (90 : ℂ))).mul (ha07597.pow 1)))

@[irreducible]
def a07599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha07599 : a07599.IsHomogeneous 39 := by
  unfold a07599
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a07600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00632 ^ 1)
theorem ha07600 : a07600.IsHomogeneous 39 := by
  unfold a07600
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a07601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00632 ^ 1)
theorem ha07601 : a07601.IsHomogeneous 33 := by
  unfold a07601
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a07602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07599 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07601 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a07600 ^ 1)
theorem ha07602 : a07602.IsHomogeneous 39 := by
  unfold a07602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07599.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07601.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha07600.pow 1)))

@[irreducible]
def a07603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00317 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha07603 : a07603.IsHomogeneous 39 := by
  unfold a07603
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a07604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00133 ^ 1 * a00207 ^ 1 * a02008 ^ 1)
theorem ha07604 : a07604.IsHomogeneous 39 := by
  unfold a07604
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07599 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07603 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07604 ^ 1)
theorem ha07605 : a07605.IsHomogeneous 39 := by
  unfold a07605
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07599.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07603.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07604.pow 1)))

@[irreducible]
def a07606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha07606 : a07606.IsHomogeneous 33 := by
  unfold a07606
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a07607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07600 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a07603 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a07606 ^ 1)
theorem ha07607 : a07607.IsHomogeneous 39 := by
  unfold a07607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha07603.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha07606.pow 1)))

@[irreducible]
def a07608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07605 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a07607 ^ 1)
theorem ha07608 : a07608.IsHomogeneous 39 := by
  unfold a07608
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07605.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha07607.pow 1)))

@[irreducible]
def a07609 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00865 ^ 1)
theorem ha07609 : a07609.IsHomogeneous 33 := by
  unfold a07609
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07610 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00865 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00324 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00865 ^ 1)
theorem ha07610 : a07610.IsHomogeneous 39 := by
  unfold a07610
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07611 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a07609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07599 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07610 ^ 1)
theorem ha07611 : a07611.IsHomogeneous 39 := by
  unfold a07611
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha07609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07599.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07610.pow 1)))

@[irreducible]
def a07612 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00058 ^ 1 * a00317 ^ 1)
theorem ha07612 : a07612.IsHomogeneous 33 := by
  unfold a07612
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07613 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a07609 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a07612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07601 ^ 1)
theorem ha07613 : a07613.IsHomogeneous 33 := by
  unfold a07613
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha07609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha07612.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07601.pow 1)))

@[irreducible]
def a07614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07611 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07613 ^ 1)
theorem ha07614 : a07614.IsHomogeneous 39 := by
  unfold a07614
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07611.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07613.pow 1)))

@[irreducible]
def a07615 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a04086 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a02008 ^ 1)
theorem ha07615 : a07615.IsHomogeneous 36 := by
  unfold a07615
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07616 : Poly := (C ((-1 : ℂ) / (28 : ℂ)) * a00003 ^ 3 * a07615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07604 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07610 ^ 1)
theorem ha07616 : a07616.IsHomogeneous 39 := by
  unfold a07616
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (28 : ℂ))).mul (ha00003.pow 3)).mul (ha07615.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07604.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07610.pow 1)))

@[irreducible]
def a07617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07611 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07616 ^ 1)
theorem ha07617 : a07617.IsHomogeneous 39 := by
  unfold a07617
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07611.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07616.pow 1)))

@[irreducible]
def a07618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07608 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07617 ^ 1)
theorem ha07618 : a07618.IsHomogeneous 39 := by
  unfold a07618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07608.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07614.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07617.pow 1)))

@[irreducible]
def a07619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01575 ^ 1)
theorem ha07619 : a07619.IsHomogeneous 36 := by
  unfold a07619
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a07620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a03363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01575 ^ 1)
theorem ha07620 : a07620.IsHomogeneous 36 := by
  unfold a07620
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a07621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07600 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07619 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07620 ^ 1)
theorem ha07621 : a07621.IsHomogeneous 39 := by
  unfold a07621
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07600.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07619.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07620.pow 1)))

@[irreducible]
def a07622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00632 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1)
theorem ha07622 : a07622.IsHomogeneous 36 := by
  unfold a07622
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a07623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07619 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a07622 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a07601 ^ 1)
theorem ha07623 : a07623.IsHomogeneous 36 := by
  unfold a07623
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha07622.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha07601.pow 1)))

@[irreducible]
def a07624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07602 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07623 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a07621 ^ 1)
theorem ha07624 : a07624.IsHomogeneous 39 := by
  unfold a07624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07602.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07623.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha07621.pow 1)))

@[irreducible]
def a07625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a03363 ^ 1)
theorem ha07625 : a07625.IsHomogeneous 36 := by
  unfold a07625
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a07626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07620 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a07625 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a07606 ^ 1)
theorem ha07626 : a07626.IsHomogeneous 36 := by
  unfold a07626
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha07625.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha07606.pow 1)))

@[irreducible]
def a07627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07621 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07626 ^ 1)
theorem ha07627 : a07627.IsHomogeneous 39 := by
  unfold a07627
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07626.pow 1)))

@[irreducible]
def a07628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07608 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07624 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a07627 ^ 1)
theorem ha07628 : a07628.IsHomogeneous 39 := by
  unfold a07628
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07608.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07624.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha07627.pow 1)))

@[irreducible]
def a07629 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1)
theorem ha07629 : a07629.IsHomogeneous 36 := by
  unfold a07629
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a07630 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a07612 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a07629 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07622 ^ 1)
theorem ha07630 : a07630.IsHomogeneous 36 := by
  unfold a07630
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha07612.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha07629.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07622.pow 1)))

@[irreducible]
def a07631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07623 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a07630 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a07613 ^ 1)
theorem ha07631 : a07631.IsHomogeneous 36 := by
  unfold a07631
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha07630.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha07613.pow 1)))

@[irreducible]
def a07632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07624 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07631 ^ 1)
theorem ha07632 : a07632.IsHomogeneous 39 := by
  unfold a07632
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07624.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07631.pow 1)))

@[irreducible]
def a07633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07628 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07632 ^ 1)
theorem ha07633 : a07633.IsHomogeneous 39 := by
  unfold a07633
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07628.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07632.pow 1)))

@[irreducible]
def a07634 : Poly := (C ((-15 : ℂ) / (1 : ℂ)) * a07598 ^ 1) + (C ((-7 : ℂ) / (18 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a07633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07535 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a07563 ^ 1)
theorem ha07634 : a07634.IsHomogeneous 54 := by
  unfold a07634
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (1 : ℂ))).mul (ha07598.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (18 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha07633.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07535.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha07563.pow 1)))

@[irreducible]
def a07635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04131 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07634 ^ 1)
theorem ha07635 : a07635.IsHomogeneous 96 := by
  unfold a07635
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04131.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07634.pow 1)))

@[irreducible]
def a07636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07496 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07635 ^ 1)
theorem ha07636 : a07636.IsHomogeneous 141 := by
  unfold a07636
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07496.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07635.pow 1)))

@[irreducible]
def a07637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07497 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07636 ^ 1)
theorem ha07637 : a07637.IsHomogeneous 183 := by
  unfold a07637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07497.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07636.pow 1)))

@[irreducible]
def a07638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07500 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07637 ^ 1)
theorem ha07638 : a07638.IsHomogeneous 225 := by
  unfold a07638
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07500.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07637.pow 1)))

@[irreducible]
def a07639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01702 ^ 1 * a02036 ^ 1) + (C ((4 : ℂ) / (243 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a03562 ^ 1)
theorem ha07639 : a07639.IsHomogeneous 135 := by
  unfold a07639
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01702.pow 1)).mul (ha02036.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (243 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a04141 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a01702 ^ 1 * a02036 ^ 1)
theorem ha07640 : a07640.IsHomogeneous 171 := by
  unfold a07640
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha04141.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)).mul (ha02036.pow 1)))

@[irreducible]
def a07641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07640 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a07639 ^ 1)
theorem ha07641 : a07641.IsHomogeneous 171 := by
  unfold a07641
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07640.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha07639.pow 1)))

@[irreducible]
def a07642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03562 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a06725 ^ 1)
theorem ha07642 : a07642.IsHomogeneous 93 := by
  unfold a07642
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03562.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a07643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07639 ^ 1) + (C ((4 : ℂ) / (243 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07642 ^ 1)
theorem ha07643 : a07643.IsHomogeneous 135 := by
  unfold a07643
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07639.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (243 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07642.pow 1)))

@[irreducible]
def a07644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07641 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a07643 ^ 1)
theorem ha07644 : a07644.IsHomogeneous 171 := by
  unfold a07644
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07641.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha07643.pow 1)))

@[irreducible]
def a07645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (243 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03562 ^ 1)
theorem ha07645 : a07645.IsHomogeneous 93 := by
  unfold a07645
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (243 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a04139 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a01702 ^ 1)
theorem ha07646 : a07646.IsHomogeneous 129 := by
  unfold a07646
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha04139.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a07647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07646 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a07645 ^ 1)
theorem ha07647 : a07647.IsHomogeneous 129 := by
  unfold a07647
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07646.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha07645.pow 1)))

@[irreducible]
def a07648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a01702 ^ 1)
theorem ha07648 : a07648.IsHomogeneous 87 := by
  unfold a07648
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a07649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha07649 : a07649.IsHomogeneous 84 := by
  unfold a07649
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a07650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07649 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha07650 : a07650.IsHomogeneous 84 := by
  unfold a07650
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07649.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a07651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07650 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07648 ^ 1)
theorem ha07651 : a07651.IsHomogeneous 126 := by
  unfold a07651
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07650.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07648.pow 1)))

@[irreducible]
def a07652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07651 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a04139 ^ 1)
theorem ha07652 : a07652.IsHomogeneous 168 := by
  unfold a07652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07651.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha04139.pow 1)))

@[irreducible]
def a07653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07652 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07646 ^ 1)
theorem ha07653 : a07653.IsHomogeneous 168 := by
  unfold a07653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07652.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07646.pow 1)))

@[irreducible]
def a07654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07653 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07647 ^ 1)
theorem ha07654 : a07654.IsHomogeneous 168 := by
  unfold a07654
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07653.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07647.pow 1)))

@[irreducible]
def a07655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07654 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a04141 ^ 1)
theorem ha07655 : a07655.IsHomogeneous 210 := by
  unfold a07655
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07654.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha04141.pow 1)))

@[irreducible]
def a07656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07655 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07640 ^ 1)
theorem ha07656 : a07656.IsHomogeneous 210 := by
  unfold a07656
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07655.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07640.pow 1)))

@[irreducible]
def a07657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07656 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07641 ^ 1)
theorem ha07657 : a07657.IsHomogeneous 210 := by
  unfold a07657
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07656.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07641.pow 1)))

@[irreducible]
def a07658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07657 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07644 ^ 1)
theorem ha07658 : a07658.IsHomogeneous 210 := by
  unfold a07658
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07657.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07644.pow 1)))

@[irreducible]
def a07659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07658 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00326 ^ 1 * a04144 ^ 1)
theorem ha07659 : a07659.IsHomogeneous 270 := by
  unfold a07659
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07658.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00326.pow 1)).mul (ha04144.pow 1)))

@[irreducible]
def a07660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07659 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07498 ^ 1)
theorem ha07660 : a07660.IsHomogeneous 270 := by
  unfold a07660
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07659.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07498.pow 1)))

@[irreducible]
def a07661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07660 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07499 ^ 1)
theorem ha07661 : a07661.IsHomogeneous 270 := by
  unfold a07661
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07660.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07499.pow 1)))

@[irreducible]
def a07662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07661 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07500 ^ 1)
theorem ha07662 : a07662.IsHomogeneous 270 := by
  unfold a07662
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07661.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07500.pow 1)))

@[irreducible]
def a07663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07662 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07638 ^ 1)
theorem ha07663 : a07663.IsHomogeneous 270 := by
  unfold a07663
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07662.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07638.pow 1)))

@[irreducible]
def a07664 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a07663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04148 ^ 1)
theorem ha07664 : a07664.IsHomogeneous 330 := by
  unfold a07664
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha07663.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04148.pow 1)))

@[irreducible]
def a07665 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a07664 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07480 ^ 1)
theorem ha07665 : a07665.IsHomogeneous 390 := by
  unfold a07665
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha07664.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07480.pow 1)))

@[irreducible]
def a07666 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00134 ^ 1 * a07665 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07481 ^ 1)
theorem ha07666 : a07666.IsHomogeneous 450 := by
  unfold a07666
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00134.pow 1)).mul (ha07665.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07481.pow 1)))

@[irreducible]
def a07667 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a07666 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07494 ^ 1)
theorem ha07667 : a07667.IsHomogeneous 510 := by
  unfold a07667
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha07666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07494.pow 1)))

@[irreducible]
def a07668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1 * a04151 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a07667 ^ 1)
theorem ha07668 : a07668.IsHomogeneous 1008 := by
  unfold a07668
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).mul (ha04151.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07667.pow 1)))

@[irreducible]
def a07669 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a07668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05708 ^ 1)
theorem ha07669 : a07669.IsHomogeneous 1395 := by
  unfold a07669
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha07668.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05708.pow 1)))

@[irreducible]
def a07670 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05709 ^ 1)
theorem ha07670 : a07670.IsHomogeneous 1752 := by
  unfold a07670
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07669.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05709.pow 1)))

@[irreducible]
def a07671 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07670 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05710 ^ 1)
theorem ha07671 : a07671.IsHomogeneous 2109 := by
  unfold a07671
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07670.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05710.pow 1)))

@[irreducible]
def a07672 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07671 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a07478 ^ 1)
theorem ha07672 : a07672.IsHomogeneous 2466 := by
  unfold a07672
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07671.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha07478.pow 1)))

@[irreducible]
def a07673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a02104 ^ 1)
theorem ha07673 : a07673.IsHomogeneous 1693 := by
  unfold a07673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha02046.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a07674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a02104 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a04232 ^ 1)
theorem ha07674 : a07674.IsHomogeneous 1276 := by
  unfold a07674
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha02104.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a07675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07673 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07674 ^ 1)
theorem ha07675 : a07675.IsHomogeneous 1693 := by
  unfold a07675
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07673.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07674.pow 1)))

@[irreducible]
def a07676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02102 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00930 ^ 1 * a02038 ^ 1)
theorem ha07676 : a07676.IsHomogeneous 271 := by
  unfold a07676
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00930.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a07677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04229 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00878 ^ 1 * a02102 ^ 1)
theorem ha07677 : a07677.IsHomogeneous 271 := by
  unfold a07677
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04229.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00878.pow 1)).mul (ha02102.pow 1)))

@[irreducible]
def a07678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07676 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a07677 ^ 1)
theorem ha07678 : a07678.IsHomogeneous 271 := by
  unfold a07678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha07677.pow 1)))

@[irreducible]
def a07679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a04144 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00930 ^ 1 * a02038 ^ 1)
theorem ha07679 : a07679.IsHomogeneous 271 := by
  unfold a07679
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha04144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00930.pow 1)).mul (ha02038.pow 1)))

end CycleQ2Concrete
