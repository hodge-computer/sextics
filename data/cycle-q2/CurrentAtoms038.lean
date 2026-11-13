import Proposal.CurrentAtoms037

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a11520 : Poly := (C ((-7 : ℂ) / (12960 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a11519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11406 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a11463 ^ 1)
theorem ha11520 : a11520.IsHomogeneous 55 := by
  unfold a11520
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (12960 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha11519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11406.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha11463.pow 1)))

@[irreducible]
def a11521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00864 ^ 1 * a01473 ^ 1)
theorem ha11521 : a11521.IsHomogeneous 36 := by
  unfold a11521
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a11522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1 * a01473 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1 * a03191 ^ 1)
theorem ha11522 : a11522.IsHomogeneous 36 := by
  unfold a11522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).mul (ha01473.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a11523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11521 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11522 ^ 1)
theorem ha11523 : a11523.IsHomogeneous 36 := by
  unfold a11523
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11521.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11522.pow 1)))

@[irreducible]
def a11524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1 * a02007 ^ 1)
theorem ha11524 : a11524.IsHomogeneous 36 := by
  unfold a11524
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11524 ^ 1)
theorem ha11525 : a11525.IsHomogeneous 36 := by
  unfold a11525
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11521.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11524.pow 1)))

@[irreducible]
def a11526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11525 ^ 1)
theorem ha11526 : a11526.IsHomogeneous 36 := by
  unfold a11526
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11523.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11525.pow 1)))

@[irreducible]
def a11527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a03191 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06158 ^ 1)
theorem ha11527 : a11527.IsHomogeneous 24 := by
  unfold a11527
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06158.pow 1)))

@[irreducible]
def a11528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11522 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11527 ^ 1)
theorem ha11528 : a11528.IsHomogeneous 36 := by
  unfold a11528
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11522.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11527.pow 1)))

@[irreducible]
def a11529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11523 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11528 ^ 1)
theorem ha11529 : a11529.IsHomogeneous 36 := by
  unfold a11529
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11523.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11528.pow 1)))

@[irreducible]
def a11530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11529 ^ 1)
theorem ha11530 : a11530.IsHomogeneous 36 := by
  unfold a11530
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11526.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11529.pow 1)))

@[irreducible]
def a11531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a04085 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a07557 ^ 1)
theorem ha11531 : a11531.IsHomogeneous 30 := by
  unfold a11531
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha07557.pow 1)))

@[irreducible]
def a11532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11531 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11524 ^ 1)
theorem ha11532 : a11532.IsHomogeneous 36 := by
  unfold a11532
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11531.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11524.pow 1)))

@[irreducible]
def a11533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11532 ^ 1)
theorem ha11533 : a11533.IsHomogeneous 36 := by
  unfold a11533
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11525.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11532.pow 1)))

@[irreducible]
def a11534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11533 ^ 1)
theorem ha11534 : a11534.IsHomogeneous 36 := by
  unfold a11534
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11526.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11533.pow 1)))

@[irreducible]
def a11535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11534 ^ 1)
theorem ha11535 : a11535.IsHomogeneous 36 := by
  unfold a11535
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11534.pow 1)))

@[irreducible]
def a11536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11376 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06158 ^ 1)
theorem ha11536 : a11536.IsHomogeneous 24 := by
  unfold a11536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11376.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06158.pow 1)))

@[irreducible]
def a11537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11536 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11527 ^ 1)
theorem ha11537 : a11537.IsHomogeneous 30 := by
  unfold a11537
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11536.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11527.pow 1)))

@[irreducible]
def a11538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11537 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11528 ^ 1)
theorem ha11538 : a11538.IsHomogeneous 36 := by
  unfold a11538
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11528.pow 1)))

@[irreducible]
def a11539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11529 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11538 ^ 1)
theorem ha11539 : a11539.IsHomogeneous 36 := by
  unfold a11539
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11538.pow 1)))

@[irreducible]
def a11540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11539 ^ 1)
theorem ha11540 : a11540.IsHomogeneous 36 := by
  unfold a11540
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11539.pow 1)))

@[irreducible]
def a11541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11540 ^ 1)
theorem ha11541 : a11541.IsHomogeneous 36 := by
  unfold a11541
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11540.pow 1)))

@[irreducible]
def a11542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01373 ^ 1)
theorem ha11542 : a11542.IsHomogeneous 45 := by
  unfold a11542
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a11543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01373 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00528 ^ 1 * a02008 ^ 1)
theorem ha11543 : a11543.IsHomogeneous 45 := by
  unfold a11543
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01373.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00528.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11542 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11543 ^ 1)
theorem ha11544 : a11544.IsHomogeneous 45 := by
  unfold a11544
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11543.pow 1)))

@[irreducible]
def a11545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a05883 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00317 ^ 1 * a03016 ^ 1)
theorem ha11545 : a11545.IsHomogeneous 45 := by
  unfold a11545
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha05883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00317.pow 1)).mul (ha03016.pow 1)))

@[irreducible]
def a11546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11542 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a11545 ^ 1)
theorem ha11546 : a11546.IsHomogeneous 45 := by
  unfold a11546
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha11545.pow 1)))

@[irreducible]
def a11547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11544 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11546 ^ 1)
theorem ha11547 : a11547.IsHomogeneous 45 := by
  unfold a11547
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11546.pow 1)))

@[irreducible]
def a11548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00528 ^ 1 * a02008 ^ 1)
theorem ha11548 : a11548.IsHomogeneous 42 := by
  unfold a11548
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11548 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a11543 ^ 1)
theorem ha11549 : a11549.IsHomogeneous 48 := by
  unfold a11549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11548.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha11543.pow 1)))

@[irreducible]
def a11550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11549 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a11544 ^ 1)
theorem ha11550 : a11550.IsHomogeneous 48 := by
  unfold a11550
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11549.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha11544.pow 1)))

@[irreducible]
def a11551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11550 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a11547 ^ 1)
theorem ha11551 : a11551.IsHomogeneous 48 := by
  unfold a11551
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11550.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha11547.pow 1)))

@[irreducible]
def a11552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a10971 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a05883 ^ 1)
theorem ha11552 : a11552.IsHomogeneous 48 := by
  unfold a11552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha10971.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha05883.pow 1)))

@[irreducible]
def a11553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11552 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11545 ^ 1)
theorem ha11553 : a11553.IsHomogeneous 48 := by
  unfold a11553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11552.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11545.pow 1)))

@[irreducible]
def a11554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11553 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11546 ^ 1)
theorem ha11554 : a11554.IsHomogeneous 48 := by
  unfold a11554
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11553.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11546.pow 1)))

@[irreducible]
def a11555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11554 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11547 ^ 1)
theorem ha11555 : a11555.IsHomogeneous 48 := by
  unfold a11555
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11554.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11547.pow 1)))

@[irreducible]
def a11556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11551 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a11555 ^ 1)
theorem ha11556 : a11556.IsHomogeneous 48 := by
  unfold a11556
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha11555.pow 1)))

@[irreducible]
def a11557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a07558 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00161 ^ 1 * a04086 ^ 1)
theorem ha11557 : a11557.IsHomogeneous 36 := by
  unfold a11557
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00161.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a11558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11548 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11557 ^ 1)
theorem ha11558 : a11558.IsHomogeneous 42 := by
  unfold a11558
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11548.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11557.pow 1)))

@[irreducible]
def a11559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11549 ^ 1)
theorem ha11559 : a11559.IsHomogeneous 48 := by
  unfold a11559
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11549.pow 1)))

@[irreducible]
def a11560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11559 ^ 1)
theorem ha11560 : a11560.IsHomogeneous 48 := by
  unfold a11560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11559.pow 1)))

@[irreducible]
def a11561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11560 ^ 1)
theorem ha11561 : a11561.IsHomogeneous 48 := by
  unfold a11561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11560.pow 1)))

@[irreducible]
def a11562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11561 ^ 1)
theorem ha11562 : a11562.IsHomogeneous 48 := by
  unfold a11562
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11561.pow 1)))

@[irreducible]
def a11563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a11562 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11541 ^ 1)
theorem ha11563 : a11563.IsHomogeneous 54 := by
  unfold a11563
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha11562.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11541.pow 1)))

@[irreducible]
def a11564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10977 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11541 ^ 1)
theorem ha11564 : a11564.IsHomogeneous 36 := by
  unfold a11564
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10977.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11541.pow 1)))

@[irreducible]
def a11565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11563 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11564 ^ 1)
theorem ha11565 : a11565.IsHomogeneous 54 := by
  unfold a11565
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11563.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11564.pow 1)))

@[irreducible]
def a11566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a11562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11563 ^ 1)
theorem ha11566 : a11566.IsHomogeneous 54 := by
  unfold a11566
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha11562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11563.pow 1)))

@[irreducible]
def a11567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11566 ^ 1)
theorem ha11567 : a11567.IsHomogeneous 54 := by
  unfold a11567
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11566.pow 1)))

@[irreducible]
def a11568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00129 ^ 1 * a01356 ^ 1)
theorem ha11568 : a11568.IsHomogeneous 39 := by
  unfold a11568
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00129.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00865 ^ 1)
theorem ha11569 : a11569.IsHomogeneous 33 := by
  unfold a11569
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1)
theorem ha11570 : a11570.IsHomogeneous 33 := by
  unfold a11570
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11570 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11568 ^ 1)
theorem ha11571 : a11571.IsHomogeneous 39 := by
  unfold a11571
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11569.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11570.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11568.pow 1)))

@[irreducible]
def a11572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00317 ^ 1 * a00520 ^ 1)
theorem ha11572 : a11572.IsHomogeneous 45 := by
  unfold a11572
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a11573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01356 ^ 1)
theorem ha11573 : a11573.IsHomogeneous 45 := by
  unfold a11573
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11572 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a11573 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11568 ^ 1)
theorem ha11574 : a11574.IsHomogeneous 45 := by
  unfold a11574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha11573.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11568.pow 1)))

@[irreducible]
def a11575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00865 ^ 1)
theorem ha11575 : a11575.IsHomogeneous 39 := by
  unfold a11575
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11572 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11569 ^ 1)
theorem ha11576 : a11576.IsHomogeneous 45 := by
  unfold a11576
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11572.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11569.pow 1)))

@[irreducible]
def a11577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11576 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11571 ^ 1)
theorem ha11577 : a11577.IsHomogeneous 45 := by
  unfold a11577
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11576.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11571.pow 1)))

@[irreducible]
def a11578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a01356 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00520 ^ 1)
theorem ha11578 : a11578.IsHomogeneous 42 := by
  unfold a11578
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a11579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a02985 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01356 ^ 1)
theorem ha11579 : a11579.IsHomogeneous 42 := by
  unfold a11579
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11578 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11579 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11568 ^ 1)
theorem ha11580 : a11580.IsHomogeneous 42 := by
  unfold a11580
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11578.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11579.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11568.pow 1)))

@[irreducible]
def a11581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00520 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1)
theorem ha11581 : a11581.IsHomogeneous 36 := by
  unfold a11581
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11578 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11570 ^ 1)
theorem ha11582 : a11582.IsHomogeneous 42 := by
  unfold a11582
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11581.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11578.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11570.pow 1)))

@[irreducible]
def a11583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11582 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11571 ^ 1)
theorem ha11583 : a11583.IsHomogeneous 42 := by
  unfold a11583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11582.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11571.pow 1)))

@[irreducible]
def a11584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a05834 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a02985 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a02985 ^ 1)
theorem ha11584 : a11584.IsHomogeneous 48 := by
  unfold a11584
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha02985.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a11585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11584 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11573 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a11579 ^ 1)
theorem ha11585 : a11585.IsHomogeneous 48 := by
  unfold a11585
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11584.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11573.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha11579.pow 1)))

@[irreducible]
def a11586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11585 ^ 1) + (C ((35 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11580 ^ 1) + (C ((45 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11574 ^ 1)
theorem ha11586 : a11586.IsHomogeneous 48 := by
  unfold a11586
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11585.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11580.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11574.pow 1)))

@[irreducible]
def a11587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11586 ^ 1) + (C ((35 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11583 ^ 1) + (C ((45 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11577 ^ 1)
theorem ha11587 : a11587.IsHomogeneous 48 := by
  unfold a11587
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11586.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11583.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11577.pow 1)))

@[irreducible]
def a11588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00317 ^ 1)
theorem ha11588 : a11588.IsHomogeneous 33 := by
  unfold a11588
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a11589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a02008 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00865 ^ 1)
theorem ha11589 : a11589.IsHomogeneous 33 := by
  unfold a11589
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11589 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11569 ^ 1)
theorem ha11590 : a11590.IsHomogeneous 39 := by
  unfold a11590
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11588.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11589.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11569.pow 1)))

@[irreducible]
def a11591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00129 ^ 1)
theorem ha11591 : a11591.IsHomogeneous 33 := by
  unfold a11591
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11588 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a11591 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11570 ^ 1)
theorem ha11592 : a11592.IsHomogeneous 39 := by
  unfold a11592
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11588.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha11591.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11570.pow 1)))

@[irreducible]
def a11593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11592 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11571 ^ 1)
theorem ha11593 : a11593.IsHomogeneous 45 := by
  unfold a11593
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11592.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11571.pow 1)))

@[irreducible]
def a11594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a02008 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a02008 ^ 1)
theorem ha11594 : a11594.IsHomogeneous 36 := by
  unfold a11594
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11594 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11575 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11589 ^ 1)
theorem ha11595 : a11595.IsHomogeneous 42 := by
  unfold a11595
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11594.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11589.pow 1)))

@[irreducible]
def a11596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11595 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11576 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11590 ^ 1)
theorem ha11596 : a11596.IsHomogeneous 48 := by
  unfold a11596
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11576.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11590.pow 1)))

@[irreducible]
def a11597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11596 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11577 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a11593 ^ 1)
theorem ha11597 : a11597.IsHomogeneous 48 := by
  unfold a11597
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11596.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11577.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha11593.pow 1)))

@[irreducible]
def a11598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00042 ^ 1)
theorem ha11598 : a11598.IsHomogeneous 36 := by
  unfold a11598
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a11599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11598 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11591 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11581 ^ 1)
theorem ha11599 : a11599.IsHomogeneous 42 := by
  unfold a11599
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11598.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11591.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11581.pow 1)))

@[irreducible]
def a11600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11599 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11592 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11582 ^ 1)
theorem ha11600 : a11600.IsHomogeneous 48 := by
  unfold a11600
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11599.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11592.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11582.pow 1)))

@[irreducible]
def a11601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11600 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11593 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11583 ^ 1)
theorem ha11601 : a11601.IsHomogeneous 48 := by
  unfold a11601
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11600.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11593.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11583.pow 1)))

@[irreducible]
def a11602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11587 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11597 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11601 ^ 1)
theorem ha11602 : a11602.IsHomogeneous 48 := by
  unfold a11602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11597.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11601.pow 1)))

@[irreducible]
def a11603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01356 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00865 ^ 1 * a01356 ^ 1)
theorem ha11603 : a11603.IsHomogeneous 45 := by
  unfold a11603
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00520 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00025 ^ 1 * a00865 ^ 1 * a01356 ^ 1)
theorem ha11604 : a11604.IsHomogeneous 45 := by
  unfold a11604
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a11605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11604 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a11603 ^ 1)
theorem ha11605 : a11605.IsHomogeneous 45 := by
  unfold a11605
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11604.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha11603.pow 1)))

@[irreducible]
def a11606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a05834 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a02985 ^ 1)
theorem ha11606 : a11606.IsHomogeneous 45 := by
  unfold a11606
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a11607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11573 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11606 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11603 ^ 1)
theorem ha11607 : a11607.IsHomogeneous 45 := by
  unfold a11607
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11606.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11603.pow 1)))

@[irreducible]
def a11608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11605 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a11607 ^ 1)
theorem ha11608 : a11608.IsHomogeneous 45 := by
  unfold a11608
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11574.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11605.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha11607.pow 1)))

@[irreducible]
def a11609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a04086 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02008 ^ 1)
theorem ha11609 : a11609.IsHomogeneous 36 := by
  unfold a11609
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02008.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11604 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11609 ^ 1)
theorem ha11610 : a11610.IsHomogeneous 45 := by
  unfold a11610
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11604.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11609.pow 1)))

@[irreducible]
def a11611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11576 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11610 ^ 1)
theorem ha11611 : a11611.IsHomogeneous 45 := by
  unfold a11611
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11576.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11605.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11610.pow 1)))

@[irreducible]
def a11612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11577 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11608 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11611 ^ 1)
theorem ha11612 : a11612.IsHomogeneous 45 := by
  unfold a11612
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11577.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11608.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11611.pow 1)))

@[irreducible]
def a11613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a10897 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a05834 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a05834 ^ 1)
theorem ha11613 : a11613.IsHomogeneous 48 := by
  unfold a11613
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha10897.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha05834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1)))

@[irreducible]
def a11614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11584 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11606 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a11613 ^ 1)
theorem ha11614 : a11614.IsHomogeneous 48 := by
  unfold a11614
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11584.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11606.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha11613.pow 1)))

@[irreducible]
def a11615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11585 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11614 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11607 ^ 1)
theorem ha11615 : a11615.IsHomogeneous 48 := by
  unfold a11615
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11585.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11614.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11607.pow 1)))

@[irreducible]
def a11616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11615 ^ 1) + (C ((45 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11608 ^ 1)
theorem ha11616 : a11616.IsHomogeneous 48 := by
  unfold a11616
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11615.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11608.pow 1)))

@[irreducible]
def a11617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11616 ^ 1) + (C ((45 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11612 ^ 1)
theorem ha11617 : a11617.IsHomogeneous 48 := by
  unfold a11617
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11616.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11612.pow 1)))

@[irreducible]
def a11618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a07558 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a04086 ^ 1)
theorem ha11618 : a11618.IsHomogeneous 36 := by
  unfold a11618
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha07558.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a11619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11594 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11618 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11609 ^ 1)
theorem ha11619 : a11619.IsHomogeneous 42 := by
  unfold a11619
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11594.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11618.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11609.pow 1)))

@[irreducible]
def a11620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11619 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11610 ^ 1)
theorem ha11620 : a11620.IsHomogeneous 48 := by
  unfold a11620
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11619.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11610.pow 1)))

@[irreducible]
def a11621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11620 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11611 ^ 1)
theorem ha11621 : a11621.IsHomogeneous 48 := by
  unfold a11621
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11620.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11611.pow 1)))

@[irreducible]
def a11622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11621 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11612 ^ 1)
theorem ha11622 : a11622.IsHomogeneous 48 := by
  unfold a11622
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11612.pow 1)))

@[irreducible]
def a11623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11617 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11622 ^ 1)
theorem ha11623 : a11623.IsHomogeneous 48 := by
  unfold a11623
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11617.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11622.pow 1)))

@[irreducible]
def a11624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a11623 ^ 1) + (C ((7 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11144 ^ 1)
theorem ha11624 : a11624.IsHomogeneous 54 := by
  unfold a11624
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha11623.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11144.pow 1)))

@[irreducible]
def a11625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11624 ^ 1) + (C ((7 : ℂ) / (108 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11145 ^ 1)
theorem ha11625 : a11625.IsHomogeneous 54 := by
  unfold a11625
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11624.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (108 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11145.pow 1)))

@[irreducible]
def a11626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00201 ^ 1 * a00864 ^ 1)
theorem ha11626 : a11626.IsHomogeneous 39 := by
  unfold a11626
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00201.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a00864 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1 * a00621 ^ 1)
theorem ha11627 : a11627.IsHomogeneous 45 := by
  unfold a11627
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a11628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a02007 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a00864 ^ 1)
theorem ha11628 : a11628.IsHomogeneous 45 := by
  unfold a11628
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11627 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a11628 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11626 ^ 1)
theorem ha11629 : a11629.IsHomogeneous 45 := by
  unfold a11629
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha11628.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11626.pow 1)))

@[irreducible]
def a11630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a01555 ^ 1)
theorem ha11630 : a11630.IsHomogeneous 33 := by
  unfold a11630
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a11631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00201 ^ 1)
theorem ha11631 : a11631.IsHomogeneous 33 := by
  unfold a11631
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a11632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11630 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11626 ^ 1)
theorem ha11632 : a11632.IsHomogeneous 39 := by
  unfold a11632
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11630.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11631.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11626.pow 1)))

@[irreducible]
def a11633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01555 ^ 1)
theorem ha11633 : a11633.IsHomogeneous 39 := by
  unfold a11633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a11634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11627 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11630 ^ 1)
theorem ha11634 : a11634.IsHomogeneous 45 := by
  unfold a11634
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11633.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11627.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11630.pow 1)))

@[irreducible]
def a11635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11629 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11634 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11632 ^ 1)
theorem ha11635 : a11635.IsHomogeneous 45 := by
  unfold a11635
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11634.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11632.pow 1)))

@[irreducible]
def a11636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha11636 : a11636.IsHomogeneous 42 := by
  unfold a11636
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a02007 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00864 ^ 1)
theorem ha11637 : a11637.IsHomogeneous 42 := by
  unfold a11637
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11636 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11637 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11626 ^ 1)
theorem ha11638 : a11638.IsHomogeneous 42 := by
  unfold a11638
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11636.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11637.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11626.pow 1)))

@[irreducible]
def a11639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a02007 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a02007 ^ 1)
theorem ha11639 : a11639.IsHomogeneous 48 := by
  unfold a11639
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11639 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11628 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a11637 ^ 1)
theorem ha11640 : a11640.IsHomogeneous 48 := by
  unfold a11640
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11639.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11628.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha11637.pow 1)))

@[irreducible]
def a11641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11640 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11629 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a11638 ^ 1)
theorem ha11641 : a11641.IsHomogeneous 48 := by
  unfold a11641
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11640.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11629.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha11638.pow 1)))

@[irreducible]
def a11642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha11642 : a11642.IsHomogeneous 36 := by
  unfold a11642
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a11643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11636 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11631 ^ 1)
theorem ha11643 : a11643.IsHomogeneous 42 := by
  unfold a11643
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11636.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11631.pow 1)))

@[irreducible]
def a11644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11638 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11643 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11632 ^ 1)
theorem ha11644 : a11644.IsHomogeneous 42 := by
  unfold a11644
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11643.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11632.pow 1)))

@[irreducible]
def a11645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11641 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11635 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a11644 ^ 1)
theorem ha11645 : a11645.IsHomogeneous 48 := by
  unfold a11645
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11641.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11635.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha11644.pow 1)))

@[irreducible]
def a11646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01555 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00621 ^ 1)
theorem ha11646 : a11646.IsHomogeneous 33 := by
  unfold a11646
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00621.pow 1)))

@[irreducible]
def a11647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03330 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01555 ^ 1)
theorem ha11647 : a11647.IsHomogeneous 33 := by
  unfold a11647
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03330.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01555.pow 1)))

@[irreducible]
def a11648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11646 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11647 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11630 ^ 1)
theorem ha11648 : a11648.IsHomogeneous 39 := by
  unfold a11648
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11646.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11647.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11630.pow 1)))

@[irreducible]
def a11649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00201 ^ 1)
theorem ha11649 : a11649.IsHomogeneous 33 := by
  unfold a11649
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)))

@[irreducible]
def a11650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11646 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a11649 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11631 ^ 1)
theorem ha11650 : a11650.IsHomogeneous 39 := by
  unfold a11650
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11646.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha11649.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11631.pow 1)))

@[irreducible]
def a11651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11648 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11650 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11632 ^ 1)
theorem ha11651 : a11651.IsHomogeneous 45 := by
  unfold a11651
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11648.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11650.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11632.pow 1)))

@[irreducible]
def a11652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03330 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a03330 ^ 1)
theorem ha11652 : a11652.IsHomogeneous 36 := by
  unfold a11652
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a11653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11652 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11633 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11647 ^ 1)
theorem ha11653 : a11653.IsHomogeneous 42 := by
  unfold a11653
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11652.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11633.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11647.pow 1)))

@[irreducible]
def a11654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11653 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11634 ^ 1) + (C ((35 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11648 ^ 1)
theorem ha11654 : a11654.IsHomogeneous 48 := by
  unfold a11654
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11653.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11634.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11648.pow 1)))

@[irreducible]
def a11655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11654 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11635 ^ 1) + (C ((35 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11651 ^ 1)
theorem ha11655 : a11655.IsHomogeneous 48 := by
  unfold a11655
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11654.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11635.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11651.pow 1)))

@[irreducible]
def a11656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00054 ^ 1)
theorem ha11656 : a11656.IsHomogeneous 36 := by
  unfold a11656
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)))

@[irreducible]
def a11657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11656 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11649 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11642 ^ 1)
theorem ha11657 : a11657.IsHomogeneous 42 := by
  unfold a11657
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11656.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11649.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11642.pow 1)))

@[irreducible]
def a11658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11657 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11650 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11643 ^ 1)
theorem ha11658 : a11658.IsHomogeneous 48 := by
  unfold a11658
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11657.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11650.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11643.pow 1)))

@[irreducible]
def a11659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11658 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11651 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11644 ^ 1)
theorem ha11659 : a11659.IsHomogeneous 48 := by
  unfold a11659
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11658.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11651.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11644.pow 1)))

@[irreducible]
def a11660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11645 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11655 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a11659 ^ 1)
theorem ha11660 : a11660.IsHomogeneous 48 := by
  unfold a11660
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11655.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha11659.pow 1)))

@[irreducible]
def a11661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00025 ^ 1 * a00864 ^ 1 * a01555 ^ 1)
theorem ha11661 : a11661.IsHomogeneous 45 := by
  unfold a11661
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a11662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a01555 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00864 ^ 1 * a01555 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a03330 ^ 1)
theorem ha11662 : a11662.IsHomogeneous 45 := by
  unfold a11662
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01555.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a11663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11662 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a11661 ^ 1)
theorem ha11663 : a11663.IsHomogeneous 45 := by
  unfold a11663
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11662.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha11661.pow 1)))

@[irreducible]
def a11664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a04085 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a02007 ^ 1)
theorem ha11664 : a11664.IsHomogeneous 45 := by
  unfold a11664
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11628 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11664 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11661 ^ 1)
theorem ha11665 : a11665.IsHomogeneous 45 := by
  unfold a11665
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11664.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11661.pow 1)))

@[irreducible]
def a11666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11629 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11663 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a11665 ^ 1)
theorem ha11666 : a11666.IsHomogeneous 45 := by
  unfold a11666
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha11665.pow 1)))

@[irreducible]
def a11667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a03330 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a06376 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1)
theorem ha11667 : a11667.IsHomogeneous 36 := by
  unfold a11667
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha06376.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a11668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11662 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11667 ^ 1)
theorem ha11668 : a11668.IsHomogeneous 45 := by
  unfold a11668
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11633.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11662.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11667.pow 1)))

@[irreducible]
def a11669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11668 ^ 1)
theorem ha11669 : a11669.IsHomogeneous 45 := by
  unfold a11669
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11668.pow 1)))

@[irreducible]
def a11670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11635 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11666 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11669 ^ 1)
theorem ha11670 : a11670.IsHomogeneous 45 := by
  unfold a11670
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11635.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11666.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11669.pow 1)))

@[irreducible]
def a11671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a07557 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a04085 ^ 1)
theorem ha11671 : a11671.IsHomogeneous 48 := by
  unfold a11671
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha07557.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a11672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11639 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11664 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a11671 ^ 1)
theorem ha11672 : a11672.IsHomogeneous 48 := by
  unfold a11672
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11639.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11664.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha11671.pow 1)))

@[irreducible]
def a11673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11640 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11672 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11665 ^ 1)
theorem ha11673 : a11673.IsHomogeneous 48 := by
  unfold a11673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11640.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11672.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11665.pow 1)))

@[irreducible]
def a11674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11641 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11673 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11666 ^ 1)
theorem ha11674 : a11674.IsHomogeneous 48 := by
  unfold a11674
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11641.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11673.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11666.pow 1)))

@[irreducible]
def a11675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11645 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11674 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11670 ^ 1)
theorem ha11675 : a11675.IsHomogeneous 48 := by
  unfold a11675
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11674.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11670.pow 1)))

@[irreducible]
def a11676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00865 ^ 1)
theorem ha11676 : a11676.IsHomogeneous 21 := by
  unfold a11676
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00865.pow 1)))

@[irreducible]
def a11677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a02008 ^ 1)
theorem ha11677 : a11677.IsHomogeneous 21 := by
  unfold a11677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha02008.pow 1)))

@[irreducible]
def a11678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11676 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11677 ^ 1)
theorem ha11678 : a11678.IsHomogeneous 21 := by
  unfold a11678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11677.pow 1)))

@[irreducible]
def a11679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00317 ^ 1)
theorem ha11679 : a11679.IsHomogeneous 21 := by
  unfold a11679
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a11680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11676 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11679 ^ 1)
theorem ha11680 : a11680.IsHomogeneous 21 := by
  unfold a11680
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11679.pow 1)))

@[irreducible]
def a11681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11680 ^ 1)
theorem ha11681 : a11681.IsHomogeneous 21 := by
  unfold a11681
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11680.pow 1)))

@[irreducible]
def a11682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00042 ^ 1)
theorem ha11682 : a11682.IsHomogeneous 24 := by
  unfold a11682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)))

@[irreducible]
def a11683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11679 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11682 ^ 1)
theorem ha11683 : a11683.IsHomogeneous 24 := by
  unfold a11683
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11682.pow 1)))

@[irreducible]
def a11684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11680 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11683 ^ 1)
theorem ha11684 : a11684.IsHomogeneous 24 := by
  unfold a11684
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11683.pow 1)))

@[irreducible]
def a11685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11681 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11684 ^ 1)
theorem ha11685 : a11685.IsHomogeneous 24 := by
  unfold a11685
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11681.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11684.pow 1)))

@[irreducible]
def a11686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a04086 ^ 1)
theorem ha11686 : a11686.IsHomogeneous 18 := by
  unfold a11686
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha04086.pow 1)))

@[irreducible]
def a11687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11677 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a11686 ^ 1)
theorem ha11687 : a11687.IsHomogeneous 21 := by
  unfold a11687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11677.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha11686.pow 1)))

@[irreducible]
def a11688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11678 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11687 ^ 1)
theorem ha11688 : a11688.IsHomogeneous 21 := by
  unfold a11688
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11687.pow 1)))

@[irreducible]
def a11689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11681 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11688 ^ 1)
theorem ha11689 : a11689.IsHomogeneous 21 := by
  unfold a11689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11681.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11688.pow 1)))

@[irreducible]
def a11690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11685 ^ 1)
theorem ha11690 : a11690.IsHomogeneous 24 := by
  unfold a11690
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11685.pow 1)))

@[irreducible]
def a11691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04086 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07558 ^ 1)
theorem ha11691 : a11691.IsHomogeneous 24 := by
  unfold a11691
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07558.pow 1)))

@[irreducible]
def a11692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11686 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11691 ^ 1)
theorem ha11692 : a11692.IsHomogeneous 24 := by
  unfold a11692
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11686.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11691.pow 1)))

@[irreducible]
def a11693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11687 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a11692 ^ 1)
theorem ha11693 : a11693.IsHomogeneous 24 := by
  unfold a11693
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha11692.pow 1)))

@[irreducible]
def a11694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11688 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11693 ^ 1)
theorem ha11694 : a11694.IsHomogeneous 24 := by
  unfold a11694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11688.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11693.pow 1)))

@[irreducible]
def a11695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11694 ^ 1)
theorem ha11695 : a11695.IsHomogeneous 24 := by
  unfold a11695
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11694.pow 1)))

@[irreducible]
def a11696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11695 ^ 1)
theorem ha11696 : a11696.IsHomogeneous 24 := by
  unfold a11696
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11690.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11695.pow 1)))

@[irreducible]
def a11697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06148 ^ 1) + (C ((7 : ℂ) / (24 : ℂ)) * a06420 ^ 1)
theorem ha11697 : a11697.IsHomogeneous 6 := by
  unfold a11697
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (24 : ℂ))).mul (ha06420.pow 1)))

@[irreducible]
def a11698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06421 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a11697 ^ 1)
theorem ha11698 : a11698.IsHomogeneous 6 := by
  unfold a11698
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha11697.pow 1)))

@[irreducible]
def a11699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11698 ^ 1)
theorem ha11699 : a11699.IsHomogeneous 6 := by
  unfold a11699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11698.pow 1)))

@[irreducible]
def a11700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11697 ^ 1)
theorem ha11700 : a11700.IsHomogeneous 6 := by
  unfold a11700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06151.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11697.pow 1)))

@[irreducible]
def a11701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11698 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a11700 ^ 1)
theorem ha11701 : a11701.IsHomogeneous 6 := by
  unfold a11701
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11698.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha11700.pow 1)))

@[irreducible]
def a11702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11699 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11701 ^ 1)
theorem ha11702 : a11702.IsHomogeneous 6 := by
  unfold a11702
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11699.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11701.pow 1)))

@[irreducible]
def a11703 : Poly := (C ((-49 : ℂ) / (4860 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11696 ^ 1)
theorem ha11703 : a11703.IsHomogeneous 24 := by
  unfold a11703
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-49 : ℂ) / (4860 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11696.pow 1)))

@[irreducible]
def a11704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a11703 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a06376 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a06376 ^ 1)
theorem ha11704 : a11704.IsHomogeneous 36 := by
  unfold a11704
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha11703.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha06376.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)))

@[irreducible]
def a11705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11652 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11667 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11704 ^ 1)
theorem ha11705 : a11705.IsHomogeneous 42 := by
  unfold a11705
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11652.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11667.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11704.pow 1)))

@[irreducible]
def a11706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11653 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11705 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11668 ^ 1)
theorem ha11706 : a11706.IsHomogeneous 48 := by
  unfold a11706
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11653.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11705.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11668.pow 1)))

@[irreducible]
def a11707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11706 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11669 ^ 1)
theorem ha11707 : a11707.IsHomogeneous 48 := by
  unfold a11707
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11706.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11669.pow 1)))

@[irreducible]
def a11708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11707 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11670 ^ 1)
theorem ha11708 : a11708.IsHomogeneous 48 := by
  unfold a11708
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11707.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11670.pow 1)))

@[irreducible]
def a11709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11675 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11708 ^ 1)
theorem ha11709 : a11709.IsHomogeneous 48 := by
  unfold a11709
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11675.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11708.pow 1)))

@[irreducible]
def a11710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a11709 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11055 ^ 1)
theorem ha11710 : a11710.IsHomogeneous 54 := by
  unfold a11710
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha11709.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11055.pow 1)))

@[irreducible]
def a11711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11710 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a11145 ^ 1)
theorem ha11711 : a11711.IsHomogeneous 54 := by
  unfold a11711
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11710.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha11145.pow 1)))

@[irreducible]
def a11712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11625 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11711 ^ 1)
theorem ha11712 : a11712.IsHomogeneous 54 := by
  unfold a11712
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11625.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11711.pow 1)))

@[irreducible]
def a11713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00207 ^ 1 * a00316 ^ 1)
theorem ha11713 : a11713.IsHomogeneous 30 := by
  unfold a11713
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a11714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a00864 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a01575 ^ 1)
theorem ha11714 : a11714.IsHomogeneous 30 := by
  unfold a11714
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha00864.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a00864 ^ 1)
theorem ha11715 : a11715.IsHomogeneous 30 := by
  unfold a11715
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11714 ^ 1) + (C ((4 : ℂ) / (49 : ℂ)) * a11715 ^ 1)
theorem ha11716 : a11716.IsHomogeneous 30 := by
  unfold a11716
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11714.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (49 : ℂ))).mul (ha11715.pow 1)))

@[irreducible]
def a11717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00632 ^ 1)
theorem ha11717 : a11717.IsHomogeneous 24 := by
  unfold a11717
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a11718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00632 ^ 1)
theorem ha11718 : a11718.IsHomogeneous 18 := by
  unfold a11718
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a11719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11713 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11718 ^ 1)
theorem ha11719 : a11719.IsHomogeneous 30 := by
  unfold a11719
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11713.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11718.pow 1)))

@[irreducible]
def a11720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00316 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha11720 : a11720.IsHomogeneous 18 := by
  unfold a11720
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11714 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11720 ^ 1)
theorem ha11721 : a11721.IsHomogeneous 30 := by
  unfold a11721
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11714.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11720.pow 1)))

@[irreducible]
def a11722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11721 ^ 1)
theorem ha11722 : a11722.IsHomogeneous 30 := by
  unfold a11722
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11719.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11721.pow 1)))

@[irreducible]
def a11723 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00864 ^ 1)
theorem ha11723 : a11723.IsHomogeneous 24 := by
  unfold a11723
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11724 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a02007 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00864 ^ 1)
theorem ha11724 : a11724.IsHomogeneous 30 := by
  unfold a11724
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a11725 : Poly := (C ((-5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11723 ^ 1) + (C ((-1 : ℂ) / (14 : ℂ)) * a11724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11713 ^ 1)
theorem ha11725 : a11725.IsHomogeneous 30 := by
  unfold a11725
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (14 : ℂ))).mul (ha11724.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11713.pow 1)))

@[irreducible]
def a11726 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a04085 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a02007 ^ 1)
theorem ha11726 : a11726.IsHomogeneous 30 := by
  unfold a11726
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha04085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11727 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a11724 ^ 1) + (C ((-1 : ℂ) / (12 : ℂ)) * a11726 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11715 ^ 1)
theorem ha11727 : a11727.IsHomogeneous 30 := by
  unfold a11727
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha11724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha11726.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11715.pow 1)))

@[irreducible]
def a11728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11725 ^ 1) + (C ((4 : ℂ) / (49 : ℂ)) * a11727 ^ 1)
theorem ha11728 : a11728.IsHomogeneous 30 := by
  unfold a11728
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11725.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (49 : ℂ))).mul (ha11727.pow 1)))

@[irreducible]
def a11729 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00058 ^ 1)
theorem ha11729 : a11729.IsHomogeneous 18 := by
  unfold a11729
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a11730 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a11729 ^ 1) + (C ((-5 : ℂ) / (24 : ℂ)) * a11723 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11718 ^ 1)
theorem ha11730 : a11730.IsHomogeneous 24 := by
  unfold a11730
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha11729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha11723.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11718.pow 1)))

@[irreducible]
def a11731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11725 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11730 ^ 1)
theorem ha11731 : a11731.IsHomogeneous 30 := by
  unfold a11731
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11719.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11725.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11730.pow 1)))

@[irreducible]
def a11732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11722 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11728 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11731 ^ 1)
theorem ha11732 : a11732.IsHomogeneous 30 := by
  unfold a11732
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11728.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11731.pow 1)))

@[irreducible]
def a11733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01575 ^ 1)
theorem ha11733 : a11733.IsHomogeneous 18 := by
  unfold a11733
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00324 ^ 1 * a01575 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01575 ^ 1)
theorem ha11734 : a11734.IsHomogeneous 18 := by
  unfold a11734
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11717 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11733 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11734 ^ 1)
theorem ha11735 : a11735.IsHomogeneous 24 := by
  unfold a11735
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11733.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11734.pow 1)))

@[irreducible]
def a11736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00632 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00207 ^ 1)
theorem ha11736 : a11736.IsHomogeneous 18 := by
  unfold a11736
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)))

@[irreducible]
def a11737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11733 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11736 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11718 ^ 1)
theorem ha11737 : a11737.IsHomogeneous 24 := by
  unfold a11737
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11733.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11736.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11718.pow 1)))

@[irreducible]
def a11738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11719 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11737 ^ 1)
theorem ha11738 : a11738.IsHomogeneous 30 := by
  unfold a11738
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11719.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11737.pow 1)))

@[irreducible]
def a11739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a03363 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03363 ^ 1)
theorem ha11739 : a11739.IsHomogeneous 18 := by
  unfold a11739
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a11740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11734 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11739 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11720 ^ 1)
theorem ha11740 : a11740.IsHomogeneous 24 := by
  unfold a11740
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11734.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11739.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11720.pow 1)))

@[irreducible]
def a11741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11721 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11740 ^ 1)
theorem ha11741 : a11741.IsHomogeneous 30 := by
  unfold a11741
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11721.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11740.pow 1)))

@[irreducible]
def a11742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11722 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11741 ^ 1)
theorem ha11742 : a11742.IsHomogeneous 30 := by
  unfold a11742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11738.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11741.pow 1)))

@[irreducible]
def a11743 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1)
theorem ha11743 : a11743.IsHomogeneous 18 := by
  unfold a11743
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)))

@[irreducible]
def a11744 : Poly := (C ((-15 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a11729 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a11743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11736 ^ 1)
theorem ha11744 : a11744.IsHomogeneous 24 := by
  unfold a11744
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha11729.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha11743.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11736.pow 1)))

@[irreducible]
def a11745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11737 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a11744 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11730 ^ 1)
theorem ha11745 : a11745.IsHomogeneous 30 := by
  unfold a11745
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11737.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha11744.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11730.pow 1)))

@[irreducible]
def a11746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11738 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11745 ^ 1)
theorem ha11746 : a11746.IsHomogeneous 30 := by
  unfold a11746
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11738.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11745.pow 1)))

@[irreducible]
def a11747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11746 ^ 1)
theorem ha11747 : a11747.IsHomogeneous 30 := by
  unfold a11747
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11742.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11746.pow 1)))

@[irreducible]
def a11748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a00864 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00864 ^ 1 * a01575 ^ 1)
theorem ha11748 : a11748.IsHomogeneous 30 := by
  unfold a11748
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00864.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a01575 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00864 ^ 1 * a01575 ^ 1)
theorem ha11749 : a11749.IsHomogeneous 24 := by
  unfold a11749
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00864.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a11750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11714 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11748 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11749 ^ 1)
theorem ha11750 : a11750.IsHomogeneous 30 := by
  unfold a11750
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11748.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11749.pow 1)))

@[irreducible]
def a11751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a02007 ^ 1)
theorem ha11751 : a11751.IsHomogeneous 30 := by
  unfold a11751
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a11752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11751 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a11748 ^ 1)
theorem ha11752 : a11752.IsHomogeneous 30 := by
  unfold a11752
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11715.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11751.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha11748.pow 1)))

@[irreducible]
def a11753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11750 ^ 1) + (C ((4 : ℂ) / (49 : ℂ)) * a11752 ^ 1)
theorem ha11753 : a11753.IsHomogeneous 30 := by
  unfold a11753
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11750.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (49 : ℂ))).mul (ha11752.pow 1)))

@[irreducible]
def a11754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06426 ^ 1)
theorem ha11754 : a11754.IsHomogeneous 18 := by
  unfold a11754
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06426.pow 1)))

@[irreducible]
def a11755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11720 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11754 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a11749 ^ 1)
theorem ha11755 : a11755.IsHomogeneous 24 := by
  unfold a11755
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11720.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11754.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha11749.pow 1)))

@[irreducible]
def a11756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11750 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11755 ^ 1)
theorem ha11756 : a11756.IsHomogeneous 30 := by
  unfold a11756
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11750.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11755.pow 1)))

@[irreducible]
def a11757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11722 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11753 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11756 ^ 1)
theorem ha11757 : a11757.IsHomogeneous 30 := by
  unfold a11757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11753.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11756.pow 1)))

@[irreducible]
def a11758 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a07557 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a04085 ^ 1)
theorem ha11758 : a11758.IsHomogeneous 30 := by
  unfold a11758
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha07557.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a11759 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a11751 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11726 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a11758 ^ 1)
theorem ha11759 : a11759.IsHomogeneous 30 := by
  unfold a11759
  exact ((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha11751.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11726.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha11758.pow 1)))

@[irreducible]
def a11760 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a11759 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11752 ^ 1)
theorem ha11760 : a11760.IsHomogeneous 30 := by
  unfold a11760
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha11759.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11727.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11752.pow 1)))

@[irreducible]
def a11761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11728 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11753 ^ 1) + (C ((4 : ℂ) / (49 : ℂ)) * a11760 ^ 1)
theorem ha11761 : a11761.IsHomogeneous 30 := by
  unfold a11761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11728.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11753.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (49 : ℂ))).mul (ha11760.pow 1)))

@[irreducible]
def a11762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11757 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11761 ^ 1)
theorem ha11762 : a11762.IsHomogeneous 30 := by
  unfold a11762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11757.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11761.pow 1)))

@[irreducible]
def a11763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha11763 : a11763.IsHomogeneous 6 := by
  unfold a11763
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11763 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha11764 : a11764.IsHomogeneous 6 := by
  unfold a11764
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00324 ^ 1)
theorem ha11765 : a11765.IsHomogeneous 6 := by
  unfold a11765
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a11766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11763 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a11765 ^ 1)
theorem ha11766 : a11766.IsHomogeneous 6 := by
  unfold a11766
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha11765.pow 1)))

@[irreducible]
def a11767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11766 ^ 1)
theorem ha11767 : a11767.IsHomogeneous 6 := by
  unfold a11767
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11766.pow 1)))

@[irreducible]
def a11768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00133 ^ 1)
theorem ha11768 : a11768.IsHomogeneous 6 := by
  unfold a11768
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)))

@[irreducible]
def a11769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11765 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11768 ^ 1)
theorem ha11769 : a11769.IsHomogeneous 6 := by
  unfold a11769
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11768.pow 1)))

@[irreducible]
def a11770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11766 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a11769 ^ 1)
theorem ha11770 : a11770.IsHomogeneous 6 := by
  unfold a11770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha11769.pow 1)))

@[irreducible]
def a11771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11770 ^ 1)
theorem ha11771 : a11771.IsHomogeneous 6 := by
  unfold a11771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11770.pow 1)))

@[irreducible]
def a11772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11764 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha11772 : a11772.IsHomogeneous 6 := by
  unfold a11772
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11772 ^ 1)
theorem ha11773 : a11773.IsHomogeneous 6 := by
  unfold a11773
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11772.pow 1)))

@[irreducible]
def a11774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11773 ^ 1)
theorem ha11774 : a11774.IsHomogeneous 6 := by
  unfold a11774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11773.pow 1)))

@[irreducible]
def a11775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03811 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11772 ^ 1)
theorem ha11775 : a11775.IsHomogeneous 6 := by
  unfold a11775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03811.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11772.pow 1)))

end CycleQ2Concrete
