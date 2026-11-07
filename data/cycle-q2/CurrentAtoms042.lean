import Proposal.CurrentAtoms041

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a12544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00121 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00717 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00280 ^ 1 * a00717 ^ 1)
theorem ha12544 : a12544.IsHomogeneous 88 := by
  unfold a12544
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00121.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00280.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a12545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00121 ^ 1 * a03590 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00280 ^ 1 * a01716 ^ 1)
theorem ha12545 : a12545.IsHomogeneous 87 := by
  unfold a12545
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00121.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00280.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12544 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12534 ^ 1)
theorem ha12546 : a12546.IsHomogeneous 88 := by
  unfold a12546
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12544.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12534.pow 1)))

@[irreducible]
def a12547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00121 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha12547 : a12547.IsHomogeneous 88 := by
  unfold a12547
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00121.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a12548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12544 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12547 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a12536 ^ 1)
theorem ha12548 : a12548.IsHomogeneous 88 := by
  unfold a12548
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha12536.pow 1)))

@[irreducible]
def a12549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12546 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12548 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12537 ^ 1)
theorem ha12549 : a12549.IsHomogeneous 88 := by
  unfold a12549
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12548.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12537.pow 1)))

@[irreducible]
def a12550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a06772 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00121 ^ 1 * a03590 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00280 ^ 1 * a03590 ^ 1)
theorem ha12550 : a12550.IsHomogeneous 90 := by
  unfold a12550
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00121.pow 1)).mul (ha03590.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12550 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a12539 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a12545 ^ 1)
theorem ha12551 : a12551.IsHomogeneous 91 := by
  unfold a12551
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha12539.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha12545.pow 1)))

@[irreducible]
def a12552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12546 ^ 1) + (C ((6 : ℂ) / (35 : ℂ)) * a12551 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12540 ^ 1)
theorem ha12552 : a12552.IsHomogeneous 91 := by
  unfold a12552
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (35 : ℂ))).mul (ha12551.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12540.pow 1)))

@[irreducible]
def a12553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12552 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12543 ^ 1)
theorem ha12553 : a12553.IsHomogeneous 91 := by
  unfold a12553
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12549.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12552.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12543.pow 1)))

@[irreducible]
def a12554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a01801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00762 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00762 ^ 1)
theorem ha12554 : a12554.IsHomogeneous 88 := by
  unfold a12554
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha01801.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a12555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00103 ^ 1 * a03728 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a01801 ^ 1)
theorem ha12555 : a12555.IsHomogeneous 87 := by
  unfold a12555
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01801.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00103.pow 1)).mul (ha03728.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a12556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12554 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12535 ^ 1)
theorem ha12556 : a12556.IsHomogeneous 88 := by
  unfold a12556
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12554.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12535.pow 1)))

@[irreducible]
def a12557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00280 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00762 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha12557 : a12557.IsHomogeneous 88 := by
  unfold a12557
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a12558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12554 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a12557 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a12536 ^ 1)
theorem ha12558 : a12558.IsHomogeneous 88 := by
  unfold a12558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha12557.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha12536.pow 1)))

@[irreducible]
def a12559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12558 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12537 ^ 1)
theorem ha12559 : a12559.IsHomogeneous 88 := by
  unfold a12559
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12558.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12537.pow 1)))

@[irreducible]
def a12560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a06991 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a03728 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1 * a03728 ^ 1)
theorem ha12560 : a12560.IsHomogeneous 90 := by
  unfold a12560
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha06991.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha03728.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha03728.pow 1)))

@[irreducible]
def a12561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12560 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a12541 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a12555 ^ 1)
theorem ha12561 : a12561.IsHomogeneous 91 := by
  unfold a12561
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12560.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha12541.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha12555.pow 1)))

@[irreducible]
def a12562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12556 ^ 1) + (C ((6 : ℂ) / (35 : ℂ)) * a12561 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12542 ^ 1)
theorem ha12562 : a12562.IsHomogeneous 91 := by
  unfold a12562
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (35 : ℂ))).mul (ha12561.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12542.pow 1)))

@[irreducible]
def a12563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12562 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a12543 ^ 1)
theorem ha12563 : a12563.IsHomogeneous 91 := by
  unfold a12563
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12562.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha12543.pow 1)))

@[irreducible]
def a12564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00121 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00103 ^ 1 * a00280 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00121 ^ 1 * a00262 ^ 1)
theorem ha12564 : a12564.IsHomogeneous 90 := by
  unfold a12564
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00121.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00103.pow 1)).mul (ha00280.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00121.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12564 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12547 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12557 ^ 1)
theorem ha12565 : a12565.IsHomogeneous 90 := by
  unfold a12565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12564.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12557.pow 1)))

@[irreducible]
def a12566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12565 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12558 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12548 ^ 1)
theorem ha12566 : a12566.IsHomogeneous 90 := by
  unfold a12566
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12565.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12558.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12548.pow 1)))

@[irreducible]
def a12567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12566 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12559 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12549 ^ 1)
theorem ha12567 : a12567.IsHomogeneous 90 := by
  unfold a12567
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12559.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12549.pow 1)))

@[irreducible]
def a12568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12567 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a12563 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a12553 ^ 1)
theorem ha12568 : a12568.IsHomogeneous 91 := by
  unfold a12568
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12567.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha12563.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha12553.pow 1)))

@[irreducible]
def a12569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00762 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00762 ^ 1 * a03590 ^ 1)
theorem ha12569 : a12569.IsHomogeneous 91 := by
  unfold a12569
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)).mul (ha01801.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00762.pow 1)).mul (ha01716.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00762.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00717 ^ 1 * a03728 ^ 1)
theorem ha12570 : a12570.IsHomogeneous 91 := by
  unfold a12570
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)).mul (ha01801.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha01801.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha03728.pow 1)))

@[irreducible]
def a12571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12538 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a12569 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a12570 ^ 1)
theorem ha12571 : a12571.IsHomogeneous 91 := by
  unfold a12571
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha12569.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha12570.pow 1)))

@[irreducible]
def a12572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00280 ^ 1 * a06772 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00025 ^ 1 * a00762 ^ 1 * a03590 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00280 ^ 1 * a03590 ^ 1)
theorem ha12572 : a12572.IsHomogeneous 88 := by
  unfold a12572
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00025.pow 1)).mul (ha00762.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12572 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12539 ^ 1) + (C ((10 : ℂ) / (9 : ℂ)) * a12569 ^ 1)
theorem ha12573 : a12573.IsHomogeneous 91 := by
  unfold a12573
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12539.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (9 : ℂ))).mul (ha12569.pow 1)))

@[irreducible]
def a12574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12540 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12571 ^ 1) + (C ((2 : ℂ) / (35 : ℂ)) * a12573 ^ 1)
theorem ha12574 : a12574.IsHomogeneous 91 := by
  unfold a12574
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12571.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (35 : ℂ))).mul (ha12573.pow 1)))

@[irreducible]
def a12575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1 * a06991 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00717 ^ 1 * a03728 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a03728 ^ 1)
theorem ha12575 : a12575.IsHomogeneous 88 := by
  unfold a12575
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha06991.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha03728.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha03728.pow 1)))

@[irreducible]
def a12576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12575 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12541 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a12570 ^ 1)
theorem ha12576 : a12576.IsHomogeneous 91 := by
  unfold a12576
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12541.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha12570.pow 1)))

@[irreducible]
def a12577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12542 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12571 ^ 1) + (C ((2 : ℂ) / (35 : ℂ)) * a12576 ^ 1)
theorem ha12577 : a12577.IsHomogeneous 91 := by
  unfold a12577
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12571.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (35 : ℂ))).mul (ha12576.pow 1)))

@[irreducible]
def a12578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12574 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12577 ^ 1)
theorem ha12578 : a12578.IsHomogeneous 91 := by
  unfold a12578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12543.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12574.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12577.pow 1)))

@[irreducible]
def a12579 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00121 ^ 1 * a12281 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a06772 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00280 ^ 1 * a06772 ^ 1)
theorem ha12579 : a12579.IsHomogeneous 90 := by
  unfold a12579
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha12281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha06772.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha06772.pow 1)))

@[irreducible]
def a12580 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12550 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12572 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12579 ^ 1)
theorem ha12580 : a12580.IsHomogeneous 90 := by
  unfold a12580
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12550.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12572.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12579.pow 1)))

@[irreducible]
def a12581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12551 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12573 ^ 1)
theorem ha12581 : a12581.IsHomogeneous 91 := by
  unfold a12581
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12580.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12551.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12573.pow 1)))

@[irreducible]
def a12582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12552 ^ 1) + (C ((6 : ℂ) / (35 : ℂ)) * a12581 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12574 ^ 1)
theorem ha12582 : a12582.IsHomogeneous 91 := by
  unfold a12582
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12552.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (35 : ℂ))).mul (ha12581.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12574.pow 1)))

@[irreducible]
def a12583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12582 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12578 ^ 1)
theorem ha12583 : a12583.IsHomogeneous 91 := by
  unfold a12583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12582.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12578.pow 1)))

@[irreducible]
def a12584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a01716 ^ 1)
theorem ha12584 : a12584.IsHomogeneous 40 := by
  unfold a12584
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01716 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a03590 ^ 1)
theorem ha12585 : a12585.IsHomogeneous 39 := by
  unfold a12585
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha03590.pow 1)))

@[irreducible]
def a12586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12584 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12585 ^ 1)
theorem ha12586 : a12586.IsHomogeneous 40 := by
  unfold a12586
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12584.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12585.pow 1)))

@[irreducible]
def a12587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00717 ^ 1)
theorem ha12587 : a12587.IsHomogeneous 40 := by
  unfold a12587
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a12588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12584 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a12587 ^ 1)
theorem ha12588 : a12588.IsHomogeneous 40 := by
  unfold a12588
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha12587.pow 1)))

@[irreducible]
def a12589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12588 ^ 1)
theorem ha12589 : a12589.IsHomogeneous 40 := by
  unfold a12589
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12586.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12588.pow 1)))

@[irreducible]
def a12590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00103 ^ 1)
theorem ha12590 : a12590.IsHomogeneous 42 := by
  unfold a12590
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)))

@[irreducible]
def a12591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12590 ^ 1)
theorem ha12591 : a12591.IsHomogeneous 42 := by
  unfold a12591
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12590.pow 1)))

@[irreducible]
def a12592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12588 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a12591 ^ 1)
theorem ha12592 : a12592.IsHomogeneous 42 := by
  unfold a12592
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12588.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha12591.pow 1)))

@[irreducible]
def a12593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12592 ^ 1)
theorem ha12593 : a12593.IsHomogeneous 42 := by
  unfold a12593
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12592.pow 1)))

@[irreducible]
def a12594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03590 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a06772 ^ 1)
theorem ha12594 : a12594.IsHomogeneous 36 := by
  unfold a12594
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha06772.pow 1)))

@[irreducible]
def a12595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12585 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a12594 ^ 1)
theorem ha12595 : a12595.IsHomogeneous 39 := by
  unfold a12595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12585.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha12594.pow 1)))

@[irreducible]
def a12596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12586 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12595 ^ 1)
theorem ha12596 : a12596.IsHomogeneous 40 := by
  unfold a12596
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12586.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12595.pow 1)))

@[irreducible]
def a12597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12596 ^ 1)
theorem ha12597 : a12597.IsHomogeneous 40 := by
  unfold a12597
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12596.pow 1)))

@[irreducible]
def a12598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12593 ^ 1)
theorem ha12598 : a12598.IsHomogeneous 42 := by
  unfold a12598
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12593.pow 1)))

@[irreducible]
def a12599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06772 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a12281 ^ 1)
theorem ha12599 : a12599.IsHomogeneous 42 := by
  unfold a12599
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha12281.pow 1)))

@[irreducible]
def a12600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12594 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a12599 ^ 1)
theorem ha12600 : a12600.IsHomogeneous 42 := by
  unfold a12600
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12594.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha12599.pow 1)))

@[irreducible]
def a12601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12595 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a12600 ^ 1)
theorem ha12601 : a12601.IsHomogeneous 42 := by
  unfold a12601
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12595.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha12600.pow 1)))

@[irreducible]
def a12602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12596 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a12601 ^ 1)
theorem ha12602 : a12602.IsHomogeneous 42 := by
  unfold a12602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha12601.pow 1)))

@[irreducible]
def a12603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12602 ^ 1)
theorem ha12603 : a12603.IsHomogeneous 42 := by
  unfold a12603
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12602.pow 1)))

@[irreducible]
def a12604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12598 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12603 ^ 1)
theorem ha12604 : a12604.IsHomogeneous 42 := by
  unfold a12604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12598.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12603.pow 1)))

@[irreducible]
def a12605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a06781 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a03597 ^ 1)
theorem ha12605 : a12605.IsHomogeneous 25 := by
  unfold a12605
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha03597.pow 1)))

@[irreducible]
def a12606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12605 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a07029 ^ 1)
theorem ha12606 : a12606.IsHomogeneous 25 := by
  unfold a12606
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12605.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha07029.pow 1)))

@[irreducible]
def a12607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12606 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a07030 ^ 1)
theorem ha12607 : a12607.IsHomogeneous 25 := by
  unfold a12607
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12606.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha07030.pow 1)))

@[irreducible]
def a12608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07031 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12607 ^ 1)
theorem ha12608 : a12608.IsHomogeneous 25 := by
  unfold a12608
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12607.pow 1)))

@[irreducible]
def a12609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12608 ^ 1)
theorem ha12609 : a12609.IsHomogeneous 25 := by
  unfold a12609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12608.pow 1)))

@[irreducible]
def a12610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a12293 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a06781 ^ 1)
theorem ha12610 : a12610.IsHomogeneous 25 := by
  unfold a12610
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha12293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha06781.pow 1)))

@[irreducible]
def a12611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12605 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12610 ^ 1)
theorem ha12611 : a12611.IsHomogeneous 25 := by
  unfold a12611
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12610.pow 1)))

@[irreducible]
def a12612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12611 ^ 1)
theorem ha12612 : a12612.IsHomogeneous 25 := by
  unfold a12612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12606.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12611.pow 1)))

@[irreducible]
def a12613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12612 ^ 1)
theorem ha12613 : a12613.IsHomogeneous 25 := by
  unfold a12613
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12612.pow 1)))

@[irreducible]
def a12614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12608 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12613 ^ 1)
theorem ha12614 : a12614.IsHomogeneous 25 := by
  unfold a12614
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12608.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12613.pow 1)))

@[irreducible]
def a12615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12614 ^ 1)
theorem ha12615 : a12615.IsHomogeneous 25 := by
  unfold a12615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12614.pow 1)))

@[irreducible]
def a12616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12604 ^ 1) + (C ((7 : ℂ) / (810 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a12615 ^ 1)
theorem ha12616 : a12616.IsHomogeneous 42 := by
  unfold a12616
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12604.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (810 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha12615.pow 1)))

@[irreducible]
def a12617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1 * a12616 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a06991 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a06991 ^ 1)
theorem ha12617 : a12617.IsHomogeneous 90 := by
  unfold a12617
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha12616.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha06991.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha06991.pow 1)))

@[irreducible]
def a12618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12560 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12575 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a12617 ^ 1)
theorem ha12618 : a12618.IsHomogeneous 90 := by
  unfold a12618
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12560.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12575.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha12617.pow 1)))

@[irreducible]
def a12619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12561 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12576 ^ 1)
theorem ha12619 : a12619.IsHomogeneous 91 := by
  unfold a12619
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12561.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12576.pow 1)))

@[irreducible]
def a12620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12562 ^ 1) + (C ((6 : ℂ) / (35 : ℂ)) * a12619 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12577 ^ 1)
theorem ha12620 : a12620.IsHomogeneous 91 := by
  unfold a12620
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (35 : ℂ))).mul (ha12619.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12577.pow 1)))

@[irreducible]
def a12621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12620 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a12578 ^ 1)
theorem ha12621 : a12621.IsHomogeneous 91 := by
  unfold a12621
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12563.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12620.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha12578.pow 1)))

@[irreducible]
def a12622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12568 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a12621 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a12583 ^ 1)
theorem ha12622 : a12622.IsHomogeneous 91 := by
  unfold a12622
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha12621.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha12583.pow 1)))

@[irreducible]
def a12623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00133 ^ 1 * a00769 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00133 ^ 1 * a00717 ^ 1 * a01816 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00324 ^ 1 * a00717 ^ 1 * a00769 ^ 1)
theorem ha12623 : a12623.IsHomogeneous 76 := by
  unfold a12623
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00133.pow 1)).mul (ha00769.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a12624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00283 ^ 1 * a00717 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a01716 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00324 ^ 1 * a00717 ^ 1 * a00769 ^ 1)
theorem ha12624 : a12624.IsHomogeneous 76 := by
  unfold a12624
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00283.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00324.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a12625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00133 ^ 1 * a00769 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00133 ^ 1 * a00283 ^ 1 * a03590 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a01716 ^ 1)
theorem ha12625 : a12625.IsHomogeneous 76 := by
  unfold a12625
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00133.pow 1)).mul (ha00769.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12625 ^ 1) + (C ((126 : ℂ) / (5 : ℂ)) * a12624 ^ 1)
theorem ha12626 : a12626.IsHomogeneous 76 := by
  unfold a12626
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12625.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((126 : ℂ) / (5 : ℂ))).mul (ha12624.pow 1)))

@[irreducible]
def a12627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00262 ^ 1 * a00324 ^ 1 * a01816 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00324 ^ 1 * a00717 ^ 1 * a00769 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00262 ^ 1 * a00769 ^ 1)
theorem ha12627 : a12627.IsHomogeneous 76 := by
  unfold a12627
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha01816.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a12628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a03756 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00133 ^ 1 * a00717 ^ 1 * a01816 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00262 ^ 1 * a00324 ^ 1 * a01816 ^ 1)
theorem ha12628 : a12628.IsHomogeneous 71 := by
  unfold a12628
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha03756.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a12629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12628 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12623 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a12627 ^ 1)
theorem ha12629 : a12629.IsHomogeneous 76 := by
  unfold a12629
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12623.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha12627.pow 1)))

@[irreducible]
def a12630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a00769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a00283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00283 ^ 1 * a00717 ^ 1)
theorem ha12630 : a12630.IsHomogeneous 71 := by
  unfold a12630
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha00283.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00283.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a12631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12630 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12624 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12627 ^ 1)
theorem ha12631 : a12631.IsHomogeneous 76 := by
  unfold a12631
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12630.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12624.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12627.pow 1)))

@[irreducible]
def a12632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12626 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a12629 ^ 1) + (C ((126 : ℂ) / (5 : ℂ)) * a12631 ^ 1)
theorem ha12632 : a12632.IsHomogeneous 76 := by
  unfold a12632
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha12629.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((126 : ℂ) / (5 : ℂ))).mul (ha12631.pow 1)))

@[irreducible]
def a12633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00769 ^ 1 * a01716 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00032 ^ 1 * a01716 ^ 1 * a01816 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00769 ^ 1 * a03590 ^ 1)
theorem ha12633 : a12633.IsHomogeneous 75 := by
  unfold a12633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00769.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00032.pow 1)).mul (ha01716.pow 1)).mul (ha01816.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00769.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00717 ^ 1 * a03756 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a01716 ^ 1 * a01816 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00133 ^ 1 * a00717 ^ 1 * a01816 ^ 1)
theorem ha12634 : a12634.IsHomogeneous 71 := by
  unfold a12634
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha03756.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha01716.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a12635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12623 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12634 ^ 1)
theorem ha12635 : a12635.IsHomogeneous 76 := by
  unfold a12635
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12633.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12623.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12634.pow 1)))

@[irreducible]
def a12636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a06772 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a03590 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00769 ^ 1 * a03590 ^ 1)
theorem ha12636 : a12636.IsHomogeneous 73 := by
  unfold a12636
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha03590.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00769.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12633 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12625 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a12636 ^ 1)
theorem ha12637 : a12637.IsHomogeneous 76 := by
  unfold a12637
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12633.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12625.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha12636.pow 1)))

@[irreducible]
def a12638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12626 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12635 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12637 ^ 1)
theorem ha12638 : a12638.IsHomogeneous 76 := by
  unfold a12638
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12635.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12637.pow 1)))

@[irreducible]
def a12639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00262 ^ 1 * a07038 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a03756 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00032 ^ 1 * a00717 ^ 1 * a03756 ^ 1)
theorem ha12639 : a12639.IsHomogeneous 71 := by
  unfold a12639
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha07038.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha03756.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha03756.pow 1)))

@[irreducible]
def a12640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12628 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12639 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12634 ^ 1)
theorem ha12640 : a12640.IsHomogeneous 71 := by
  unfold a12640
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12639.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12634.pow 1)))

@[irreducible]
def a12641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12640 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12629 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12635 ^ 1)
theorem ha12641 : a12641.IsHomogeneous 76 := by
  unfold a12641
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12640.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12629.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12635.pow 1)))

@[irreducible]
def a12642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12638 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a12641 ^ 1)
theorem ha12642 : a12642.IsHomogeneous 76 := by
  unfold a12642
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12638.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha12641.pow 1)))

@[irreducible]
def a12643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00122 ^ 1 * a00324 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a01716 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00122 ^ 1 * a01716 ^ 1)
theorem ha12643 : a12643.IsHomogeneous 76 := by
  unfold a12643
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha03590.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00122.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00122 ^ 1 * a01716 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00283 ^ 1 * a00717 ^ 1)
theorem ha12644 : a12644.IsHomogeneous 71 := by
  unfold a12644
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00122.pow 1)).mul (ha01716.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00283.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a12645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12644 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a12643 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a12624 ^ 1)
theorem ha12645 : a12645.IsHomogeneous 76 := by
  unfold a12645
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha12643.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha12624.pow 1)))

@[irreducible]
def a12646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a06772 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a03590 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00122 ^ 1 * a00324 ^ 1 * a03590 ^ 1)
theorem ha12646 : a12646.IsHomogeneous 73 := by
  unfold a12646
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12646 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a12625 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a12643 ^ 1)
theorem ha12647 : a12647.IsHomogeneous 76 := by
  unfold a12647
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha12625.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha12643.pow 1)))

@[irreducible]
def a12648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12626 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12647 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a12645 ^ 1)
theorem ha12648 : a12648.IsHomogeneous 76 := by
  unfold a12648
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12647.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha12645.pow 1)))

@[irreducible]
def a12649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00262 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00262 ^ 1 * a00283 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00122 ^ 1 * a00717 ^ 1)
theorem ha12649 : a12649.IsHomogeneous 71 := by
  unfold a12649
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00262.pow 1)).mul (ha00283.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00122.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a12650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12630 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a12649 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a12644 ^ 1)
theorem ha12650 : a12650.IsHomogeneous 71 := by
  unfold a12650
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12630.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha12649.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha12644.pow 1)))

@[irreducible]
def a12651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12650 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12631 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a12645 ^ 1)
theorem ha12651 : a12651.IsHomogeneous 76 := by
  unfold a12651
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12650.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12631.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha12645.pow 1)))

@[irreducible]
def a12652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12648 ^ 1) + (C ((126 : ℂ) / (5 : ℂ)) * a12651 ^ 1)
theorem ha12652 : a12652.IsHomogeneous 76 := by
  unfold a12652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12648.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((126 : ℂ) / (5 : ℂ))).mul (ha12651.pow 1)))

@[irreducible]
def a12653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00122 ^ 1 * a12281 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a06772 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a06772 ^ 1)
theorem ha12653 : a12653.IsHomogeneous 73 := by
  unfold a12653
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha12281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha06772.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha06772.pow 1)))

@[irreducible]
def a12654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12636 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12646 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a12653 ^ 1)
theorem ha12654 : a12654.IsHomogeneous 73 := by
  unfold a12654
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12636.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12646.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha12653.pow 1)))

@[irreducible]
def a12655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12654 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12647 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a12637 ^ 1)
theorem ha12655 : a12655.IsHomogeneous 76 := by
  unfold a12655
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12647.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha12637.pow 1)))

@[irreducible]
def a12656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12638 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12648 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12655 ^ 1)
theorem ha12656 : a12656.IsHomogeneous 76 := by
  unfold a12656
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12648.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12655.pow 1)))

@[irreducible]
def a12657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12656 ^ 1)
theorem ha12657 : a12657.IsHomogeneous 76 := by
  unfold a12657
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12652.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12656.pow 1)))

@[irreducible]
def a12658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00324 ^ 1 * a03756 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a01816 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00324 ^ 1 * a01816 ^ 1)
theorem ha12658 : a12658.IsHomogeneous 73 := by
  unfold a12658
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha03756.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha01816.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a12659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00769 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a01816 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00769 ^ 1)
theorem ha12659 : a12659.IsHomogeneous 72 := by
  unfold a12659
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a12660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12658 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12627 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 4 * a12659 ^ 1)
theorem ha12660 : a12660.IsHomogeneous 76 := by
  unfold a12660
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12658.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12627.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 4)).mul (ha12659.pow 1)))

@[irreducible]
def a12661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a07038 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00133 ^ 1 * a00262 ^ 1 * a03756 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00324 ^ 1 * a03756 ^ 1)
theorem ha12661 : a12661.IsHomogeneous 73 := by
  unfold a12661
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha07038.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha03756.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha03756.pow 1)))

@[irreducible]
def a12662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12658 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12661 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 2 * a12628 ^ 1)
theorem ha12662 : a12662.IsHomogeneous 73 := by
  unfold a12662
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12658.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12661.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 2)).mul (ha12628.pow 1)))

@[irreducible]
def a12663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12660 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a12629 ^ 1)
theorem ha12663 : a12663.IsHomogeneous 76 := by
  unfold a12663
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12660.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha12629.pow 1)))

@[irreducible]
def a12664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00283 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00769 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00283 ^ 1)
theorem ha12664 : a12664.IsHomogeneous 73 := by
  unfold a12664
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00769.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a12665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12664 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a12659 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12630 ^ 1)
theorem ha12665 : a12665.IsHomogeneous 73 := by
  unfold a12665
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12664.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha12659.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12630.pow 1)))

@[irreducible]
def a12666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12665 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12660 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12631 ^ 1)
theorem ha12666 : a12666.IsHomogeneous 76 := by
  unfold a12666
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12665.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12660.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12631.pow 1)))

@[irreducible]
def a12667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12632 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a12663 ^ 1) + (C ((28 : ℂ) / (5 : ℂ)) * a12666 ^ 1)
theorem ha12667 : a12667.IsHomogeneous 76 := by
  unfold a12667
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha12663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (5 : ℂ))).mul (ha12666.pow 1)))

@[irreducible]
def a12668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00721 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 5 * a01721 ^ 1)
theorem ha12668 : a12668.IsHomogeneous 24 := by
  unfold a12668
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 5)).mul (ha01721.pow 1)))

@[irreducible]
def a12669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03597 ^ 1)
theorem ha12669 : a12669.IsHomogeneous 19 := by
  unfold a12669
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03597.pow 1)))

@[irreducible]
def a12670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12668 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 5 * a12669 ^ 1)
theorem ha12670 : a12670.IsHomogeneous 24 := by
  unfold a12670
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12668.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 5)).mul (ha12669.pow 1)))

@[irreducible]
def a12671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha12671 : a12671.IsHomogeneous 25 := by
  unfold a12671
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a12672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12671 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12668 ^ 1)
theorem ha12672 : a12672.IsHomogeneous 25 := by
  unfold a12672
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12671.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12668.pow 1)))

@[irreducible]
def a12673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12672 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12670 ^ 1)
theorem ha12673 : a12673.IsHomogeneous 25 := by
  unfold a12673
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12672.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12670.pow 1)))

@[irreducible]
def a12674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00264 ^ 1)
theorem ha12674 : a12674.IsHomogeneous 25 := by
  unfold a12674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)))

@[irreducible]
def a12675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12671 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a12674 ^ 1)
theorem ha12675 : a12675.IsHomogeneous 25 := by
  unfold a12675
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12671.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha12674.pow 1)))

@[irreducible]
def a12676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12675 ^ 1)
theorem ha12676 : a12676.IsHomogeneous 25 := by
  unfold a12676
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12675.pow 1)))

@[irreducible]
def a12677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12673 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12676 ^ 1)
theorem ha12677 : a12677.IsHomogeneous 25 := by
  unfold a12677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12673.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12676.pow 1)))

@[irreducible]
def a12678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03597 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a06781 ^ 1)
theorem ha12678 : a12678.IsHomogeneous 19 := by
  unfold a12678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha06781.pow 1)))

@[irreducible]
def a12679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12678 ^ 1)
theorem ha12679 : a12679.IsHomogeneous 19 := by
  unfold a12679
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12678.pow 1)))

@[irreducible]
def a12680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12670 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 5 * a12679 ^ 1)
theorem ha12680 : a12680.IsHomogeneous 24 := by
  unfold a12680
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12670.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 5)).mul (ha12679.pow 1)))

@[irreducible]
def a12681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12673 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12680 ^ 1)
theorem ha12681 : a12681.IsHomogeneous 25 := by
  unfold a12681
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12673.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12680.pow 1)))

@[irreducible]
def a12682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12677 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12681 ^ 1)
theorem ha12682 : a12682.IsHomogeneous 25 := by
  unfold a12682
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12677.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12681.pow 1)))

@[irreducible]
def a12683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a12293 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06781 ^ 1)
theorem ha12683 : a12683.IsHomogeneous 25 := by
  unfold a12683
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha12293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06781.pow 1)))

@[irreducible]
def a12684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12683 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12678 ^ 1)
theorem ha12684 : a12684.IsHomogeneous 25 := by
  unfold a12684
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12683.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12678.pow 1)))

@[irreducible]
def a12685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12684 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12679 ^ 1)
theorem ha12685 : a12685.IsHomogeneous 25 := by
  unfold a12685
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12684.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12679.pow 1)))

@[irreducible]
def a12686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12685 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12680 ^ 1)
theorem ha12686 : a12686.IsHomogeneous 25 := by
  unfold a12686
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12685.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12680.pow 1)))

@[irreducible]
def a12687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12681 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12686 ^ 1)
theorem ha12687 : a12687.IsHomogeneous 25 := by
  unfold a12687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12681.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12686.pow 1)))

@[irreducible]
def a12688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12682 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12687 ^ 1)
theorem ha12688 : a12688.IsHomogeneous 25 := by
  unfold a12688
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12682.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12687.pow 1)))

@[irreducible]
def a12689 : Poly := (C ((-7 : ℂ) / (54 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a11369 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12688 ^ 1)
theorem ha12689 : a12689.IsHomogeneous 25 := by
  unfold a12689
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha11369.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12688.pow 1)))

@[irreducible]
def a12690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00103 ^ 1 * a12689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a07038 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00262 ^ 1 * a07038 ^ 1)
theorem ha12690 : a12690.IsHomogeneous 73 := by
  unfold a12690
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha12689.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha07038.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha07038.pow 1)))

@[irreducible]
def a12691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12661 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12690 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12639 ^ 1)
theorem ha12691 : a12691.IsHomogeneous 73 := by
  unfold a12691
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12661.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12690.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12639.pow 1)))

@[irreducible]
def a12692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12662 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12691 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 2 * a12640 ^ 1)
theorem ha12692 : a12692.IsHomogeneous 73 := by
  unfold a12692
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12691.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 2)).mul (ha12640.pow 1)))

@[irreducible]
def a12693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12692 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12663 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a12641 ^ 1)
theorem ha12693 : a12693.IsHomogeneous 76 := by
  unfold a12693
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12692.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha12641.pow 1)))

@[irreducible]
def a12694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12667 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a12693 ^ 1)
theorem ha12694 : a12694.IsHomogeneous 76 := by
  unfold a12694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12642.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12667.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha12693.pow 1)))

@[irreducible]
def a12695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00283 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00122 ^ 1 * a00262 ^ 1)
theorem ha12695 : a12695.IsHomogeneous 73 := by
  unfold a12695
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00122.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12664 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12695 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12649 ^ 1)
theorem ha12696 : a12696.IsHomogeneous 73 := by
  unfold a12696
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12664.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12695.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12649.pow 1)))

@[irreducible]
def a12697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12665 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12696 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12650 ^ 1)
theorem ha12697 : a12697.IsHomogeneous 73 := by
  unfold a12697
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12665.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12696.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12650.pow 1)))

@[irreducible]
def a12698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12666 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12651 ^ 1)
theorem ha12698 : a12698.IsHomogeneous 76 := by
  unfold a12698
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12666.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12651.pow 1)))

@[irreducible]
def a12699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12667 ^ 1) + (C ((28 : ℂ) / (5 : ℂ)) * a12698 ^ 1)
theorem ha12699 : a12699.IsHomogeneous 76 := by
  unfold a12699
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12652.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12667.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (5 : ℂ))).mul (ha12698.pow 1)))

@[irreducible]
def a12700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12657 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12699 ^ 1)
theorem ha12700 : a12700.IsHomogeneous 76 := by
  unfold a12700
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12657.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12694.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12699.pow 1)))

@[irreducible]
def a12701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a12533 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a12700 ^ 1) + (C ((21 : ℂ) / (10 : ℂ)) * a00000 ^ 1 * a12622 ^ 1)
theorem ha12701 : a12701.IsHomogeneous 92 := by
  unfold a12701
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha12533.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha12700.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (10 : ℂ))).mul (ha00000.pow 1)).mul (ha12622.pow 1)))

@[irreducible]
def a12702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00262 ^ 1 * a07048 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a07048 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a12701 ^ 1)
theorem ha12702 : a12702.IsHomogeneous 140 := by
  unfold a12702
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00262.pow 1)).mul (ha07048.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha07048.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha12701.pow 1)))

@[irreducible]
def a12703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a12388 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a12702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a12399 ^ 1)
theorem ha12703 : a12703.IsHomogeneous 182 := by
  unfold a12703
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha12388.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha12702.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha12399.pow 1)))

@[irreducible]
def a12704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12389 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a12703 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a12400 ^ 1)
theorem ha12704 : a12704.IsHomogeneous 182 := by
  unfold a12704
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha12703.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha12400.pow 1)))

@[irreducible]
def a12705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12390 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a12401 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a12704 ^ 1)
theorem ha12705 : a12705.IsHomogeneous 182 := by
  unfold a12705
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha12401.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha12704.pow 1)))

@[irreducible]
def a12706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12391 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12705 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a12402 ^ 1)
theorem ha12706 : a12706.IsHomogeneous 182 := by
  unfold a12706
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12391.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12705.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha12402.pow 1)))

@[irreducible]
def a12707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12706 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a12416 ^ 1)
theorem ha12707 : a12707.IsHomogeneous 182 := by
  unfold a12707
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12392.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12706.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha12416.pow 1)))

@[irreducible]
def a12708 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a07053 ^ 1)
theorem ha12708 : a12708.IsHomogeneous 328 := by
  unfold a12708
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12707.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha07053.pow 1)))

@[irreducible]
def a12709 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12708 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12331 ^ 1)
theorem ha12709 : a12709.IsHomogeneous 474 := by
  unfold a12709
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12708.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12331.pow 1)))

@[irreducible]
def a12710 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12332 ^ 1)
theorem ha12710 : a12710.IsHomogeneous 620 := by
  unfold a12710
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12709.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12332.pow 1)))

@[irreducible]
def a12711 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12333 ^ 1)
theorem ha12711 : a12711.IsHomogeneous 766 := by
  unfold a12711
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12710.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12333.pow 1)))

@[irreducible]
def a12712 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12711 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12357 ^ 1)
theorem ha12712 : a12712.IsHomogeneous 870 := by
  unfold a12712
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12711.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12357.pow 1)))

@[irreducible]
def a12713 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1 * a07057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a12712 ^ 1)
theorem ha12713 : a12713.IsHomogeneous 949 := by
  unfold a12713
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).mul (ha07057.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha12712.pow 1)))

@[irreducible]
def a12714 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12713 ^ 1)
theorem ha12714 : a12714.IsHomogeneous 1004 := by
  unfold a12714
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12713.pow 1)))

@[irreducible]
def a12715 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12714 ^ 1)
theorem ha12715 : a12715.IsHomogeneous 1059 := by
  unfold a12715
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12254.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12714.pow 1)))

@[irreducible]
def a12716 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12715 ^ 1)
theorem ha12716 : a12716.IsHomogeneous 1059 := by
  unfold a12716
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12715.pow 1)))

@[irreducible]
def a12717 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12716 ^ 1)
theorem ha12717 : a12717.IsHomogeneous 1059 := by
  unfold a12717
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12716.pow 1)))

@[irreducible]
def a12718 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12717 ^ 1)
theorem ha12718 : a12718.IsHomogeneous 1059 := by
  unfold a12718
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12717.pow 1)))

@[irreducible]
def a12719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12718 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00291 ^ 1 * a07062 ^ 1)
theorem ha12719 : a12719.IsHomogeneous 1174 := by
  unfold a12719
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12718.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00291.pow 1)).mul (ha07062.pow 1)))

@[irreducible]
def a12720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12719 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12240 ^ 1)
theorem ha12720 : a12720.IsHomogeneous 1289 := by
  unfold a12720
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12719.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12240.pow 1)))

@[irreducible]
def a12721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12720 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12241 ^ 1)
theorem ha12721 : a12721.IsHomogeneous 1404 := by
  unfold a12721
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12720.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12241.pow 1)))

@[irreducible]
def a12722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12721 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12242 ^ 1)
theorem ha12722 : a12722.IsHomogeneous 1464 := by
  unfold a12722
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12242.pow 1)))

@[irreducible]
def a12723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12722 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12246 ^ 1)
theorem ha12723 : a12723.IsHomogeneous 1524 := by
  unfold a12723
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12246.pow 1)))

@[irreducible]
def a12724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01866 ^ 1 * a03783 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01833 ^ 1 * a03844 ^ 1)
theorem ha12724 : a12724.IsHomogeneous 1133 := by
  unfold a12724
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01866.pow 1)).mul (ha03783.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01833.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a12725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a07079 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1 * a03783 ^ 1)
theorem ha12725 : a12725.IsHomogeneous 1248 := by
  unfold a12725
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha07079.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)).mul (ha03783.pow 1)))

@[irreducible]
def a12726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12725 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12724 ^ 1)
theorem ha12726 : a12726.IsHomogeneous 1248 := by
  unfold a12726
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12725.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12724.pow 1)))

@[irreducible]
def a12727 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a07183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01833 ^ 1 * a03844 ^ 1)
theorem ha12727 : a12727.IsHomogeneous 1018 := by
  unfold a12727
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha07183.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01833.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a12728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12724 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12727 ^ 1)
theorem ha12728 : a12728.IsHomogeneous 1133 := by
  unfold a12728
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12724.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12727.pow 1)))

@[irreducible]
def a12729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12726 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12728 ^ 1)
theorem ha12729 : a12729.IsHomogeneous 1248 := by
  unfold a12729
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12726.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12728.pow 1)))

@[irreducible]
def a12730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01866 ^ 1 * a03781 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a03844 ^ 1)
theorem ha12730 : a12730.IsHomogeneous 915 := by
  unfold a12730
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01866.pow 1)).mul (ha03781.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a12731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a07076 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1 * a03781 ^ 1)
theorem ha12731 : a12731.IsHomogeneous 1030 := by
  unfold a12731
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha07076.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)).mul (ha03781.pow 1)))

@[irreducible]
def a12732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12731 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12730 ^ 1)
theorem ha12732 : a12732.IsHomogeneous 1030 := by
  unfold a12732
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12731.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12730.pow 1)))

@[irreducible]
def a12733 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a03844 ^ 1)
theorem ha12733 : a12733.IsHomogeneous 800 := by
  unfold a12733
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07183.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a12734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12730 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12733 ^ 1)
theorem ha12734 : a12734.IsHomogeneous 915 := by
  unfold a12734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12730.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12733.pow 1)))

@[irreducible]
def a12735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12732 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12734 ^ 1)
theorem ha12735 : a12735.IsHomogeneous 1030 := by
  unfold a12735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12732.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12734.pow 1)))

@[irreducible]
def a12736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a01866 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03844 ^ 1)
theorem ha12736 : a12736.IsHomogeneous 697 := by
  unfold a12736
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha01866.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a12737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a07074 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a01866 ^ 1)
theorem ha12737 : a12737.IsHomogeneous 812 := by
  unfold a12737
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha07074.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a12738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12737 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12736 ^ 1)
theorem ha12738 : a12738.IsHomogeneous 812 := by
  unfold a12738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12737.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12736.pow 1)))

@[irreducible]
def a12739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a00792 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1)
theorem ha12739 : a12739.IsHomogeneous 594 := by
  unfold a12739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha00792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a12740 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 2)
theorem ha12740 : a12740.IsHomogeneous 436 := by
  unfold a12740
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 2)))

@[irreducible]
def a12741 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12740 ^ 1)
theorem ha12741 : a12741.IsHomogeneous 436 := by
  unfold a12741
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12740.pow 1)))

@[irreducible]
def a12742 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a12741 ^ 1)
theorem ha12742 : a12742.IsHomogeneous 654 := by
  unfold a12742
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12739.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha12741.pow 1)))

@[irreducible]
def a12743 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a07074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a12742 ^ 1)
theorem ha12743 : a12743.IsHomogeneous 872 := by
  unfold a12743
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha07074.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha12742.pow 1)))

@[irreducible]
def a12744 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12737 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12743 ^ 1)
theorem ha12744 : a12744.IsHomogeneous 872 := by
  unfold a12744
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12737.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12743.pow 1)))

@[irreducible]
def a12745 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12744 ^ 1)
theorem ha12745 : a12745.IsHomogeneous 872 := by
  unfold a12745
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12744.pow 1)))

@[irreducible]
def a12746 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a07076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a12745 ^ 1)
theorem ha12746 : a12746.IsHomogeneous 1090 := by
  unfold a12746
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha07076.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha12745.pow 1)))

@[irreducible]
def a12747 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12746 ^ 1)
theorem ha12747 : a12747.IsHomogeneous 1090 := by
  unfold a12747
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12746.pow 1)))

@[irreducible]
def a12748 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12747 ^ 1)
theorem ha12748 : a12748.IsHomogeneous 1090 := by
  unfold a12748
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12747.pow 1)))

@[irreducible]
def a12749 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12748 ^ 1)
theorem ha12749 : a12749.IsHomogeneous 1090 := by
  unfold a12749
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12748.pow 1)))

@[irreducible]
def a12750 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a07079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a12749 ^ 1)
theorem ha12750 : a12750.IsHomogeneous 1308 := by
  unfold a12750
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha07079.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha12749.pow 1)))

@[irreducible]
def a12751 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12750 ^ 1)
theorem ha12751 : a12751.IsHomogeneous 1308 := by
  unfold a12751
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12725.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12750.pow 1)))

@[irreducible]
def a12752 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12726 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12751 ^ 1)
theorem ha12752 : a12752.IsHomogeneous 1308 := by
  unfold a12752
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12751.pow 1)))

@[irreducible]
def a12753 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12729 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12752 ^ 1)
theorem ha12753 : a12753.IsHomogeneous 1308 := by
  unfold a12753
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12752.pow 1)))

@[irreducible]
def a12754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01855 ^ 1 * a01863 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00790 ^ 1 * a03823 ^ 1)
theorem ha12754 : a12754.IsHomogeneous 484 := by
  unfold a12754
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01855.pow 1)).mul (ha01863.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00790.pow 1)).mul (ha03823.pow 1)))

@[irreducible]
def a12755 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01855 ^ 1 * a01863 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00787 ^ 1 * a03840 ^ 1)
theorem ha12755 : a12755.IsHomogeneous 576 := by
  unfold a12755
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01855.pow 1)).mul (ha01863.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00787.pow 1)).mul (ha03840.pow 1)))

@[irreducible]
def a12756 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12755 ^ 1)
theorem ha12756 : a12756.IsHomogeneous 582 := by
  unfold a12756
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12755.pow 1)))

@[irreducible]
def a12757 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a07148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00790 ^ 1 * a03823 ^ 1)
theorem ha12757 : a12757.IsHomogeneous 392 := by
  unfold a12757
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha07148.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00790.pow 1)).mul (ha03823.pow 1)))

@[irreducible]
def a12758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12754 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12757 ^ 1)
theorem ha12758 : a12758.IsHomogeneous 490 := by
  unfold a12758
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12757.pow 1)))

@[irreducible]
def a12759 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12758 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12756 ^ 1)
theorem ha12759 : a12759.IsHomogeneous 588 := by
  unfold a12759
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12758.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12756.pow 1)))

@[irreducible]
def a12760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00787 ^ 1 * a03840 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00290 ^ 1 * a07178 ^ 1)
theorem ha12760 : a12760.IsHomogeneous 667 := by
  unfold a12760
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00787.pow 1)).mul (ha03840.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00290.pow 1)).mul (ha07178.pow 1)))

@[irreducible]
def a12761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12755 ^ 1)
theorem ha12761 : a12761.IsHomogeneous 673 := by
  unfold a12761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12760.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12755.pow 1)))

@[irreducible]
def a12762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12756 ^ 1)
theorem ha12762 : a12762.IsHomogeneous 679 := by
  unfold a12762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12761.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12756.pow 1)))

@[irreducible]
def a12763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12759 ^ 1)
theorem ha12763 : a12763.IsHomogeneous 685 := by
  unfold a12763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12762.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12759.pow 1)))

@[irreducible]
def a12764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00265 ^ 1 * a00783 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00783 ^ 1 * a00785 ^ 1)
theorem ha12764 : a12764.IsHomogeneous 180 := by
  unfold a12764
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).mul (ha01841.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1)))

@[irreducible]
def a12765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00289 ^ 1 * a00785 ^ 1 * a01841 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00783 ^ 1 * a00785 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00155 ^ 1 * a00289 ^ 1 * a01852 ^ 1)
theorem ha12765 : a12765.IsHomogeneous 180 := by
  unfold a12765
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00289.pow 1)).mul (ha00785.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a03803 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1 * a01841 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00783 ^ 1 * a01841 ^ 1)
theorem ha12766 : a12766.IsHomogeneous 186 := by
  unfold a12766
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha03803.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1)).mul (ha01841.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a12767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12766 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12765 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12764 ^ 1)
theorem ha12767 : a12767.IsHomogeneous 186 := by
  unfold a12767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12766.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12765.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12764.pow 1)))

@[irreducible]
def a12768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00783 ^ 1 * a00785 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00785 ^ 1 * a01848 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00783 ^ 1 * a01852 ^ 1)
theorem ha12768 : a12768.IsHomogeneous 174 := by
  unfold a12768
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha01848.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00785 ^ 1 * a01848 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a03812 ^ 1)
theorem ha12769 : a12769.IsHomogeneous 173 := by
  unfold a12769
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha01848.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha03812.pow 1)))

@[irreducible]
def a12770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12764 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12768 ^ 1)
theorem ha12770 : a12770.IsHomogeneous 180 := by
  unfold a12770
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12764.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12768.pow 1)))

@[irreducible]
def a12771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a01852 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00289 ^ 1 * a01852 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a03819 ^ 1)
theorem ha12771 : a12771.IsHomogeneous 173 := by
  unfold a12771
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha01852.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12765 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12768 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12771 ^ 1)
theorem ha12772 : a12772.IsHomogeneous 180 := by
  unfold a12772
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12765.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12768.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12771.pow 1)))

@[irreducible]
def a12773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12767 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12772 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12770 ^ 1)
theorem ha12773 : a12773.IsHomogeneous 186 := by
  unfold a12773
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12767.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12772.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12770.pow 1)))

@[irreducible]
def a12774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00783 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a01841 ^ 1 * a01848 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00783 ^ 1 * a01841 ^ 1)
theorem ha12774 : a12774.IsHomogeneous 131 := by
  unfold a12774
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00783.pow 1)).mul (ha03803.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01841.pow 1)).mul (ha01848.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a12775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a01841 ^ 1 * a01848 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a03812 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a01848 ^ 1)
theorem ha12775 : a12775.IsHomogeneous 124 := by
  unfold a12775
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha01841.pow 1)).mul (ha01848.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha03812.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)))

@[irreducible]
def a12776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12774 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a12775 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12764 ^ 1)
theorem ha12776 : a12776.IsHomogeneous 186 := by
  unfold a12776
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12774.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12775.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12764.pow 1)))

@[irreducible]
def a12777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00289 ^ 1 * a07120 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00783 ^ 1 * a03803 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a03803 ^ 1)
theorem ha12777 : a12777.IsHomogeneous 137 := by
  unfold a12777
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha07120.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00783.pow 1)).mul (ha03803.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a12778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12777 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a12774 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12766 ^ 1)
theorem ha12778 : a12778.IsHomogeneous 192 := by
  unfold a12778
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12777.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12774.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12766.pow 1)))

@[irreducible]
def a12779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12778 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12776 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12767 ^ 1)
theorem ha12779 : a12779.IsHomogeneous 192 := by
  unfold a12779
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12778.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12776.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12767.pow 1)))

@[irreducible]
def a12780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a03812 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a07133 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a03812 ^ 1)
theorem ha12780 : a12780.IsHomogeneous 117 := by
  unfold a12780
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha03812.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha03812.pow 1)))

@[irreducible]
def a12781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12775 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a12780 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12769 ^ 1)
theorem ha12781 : a12781.IsHomogeneous 179 := by
  unfold a12781
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12775.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12780.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12769.pow 1)))

@[irreducible]
def a12782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12776 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12781 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12770 ^ 1)
theorem ha12782 : a12782.IsHomogeneous 186 := by
  unfold a12782
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12776.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12781.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12770.pow 1)))

@[irreducible]
def a12783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12779 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12782 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12773 ^ 1)
theorem ha12783 : a12783.IsHomogeneous 192 := by
  unfold a12783
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12782.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12773.pow 1)))

@[irreducible]
def a12784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00785 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1 * a01841 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a01841 ^ 1 * a01852 ^ 1)
theorem ha12784 : a12784.IsHomogeneous 188 := by
  unfold a12784
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00785.pow 1)).mul (ha03803.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1)).mul (ha01841.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha01841.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01841 ^ 1 * a01852 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00155 ^ 1 * a00289 ^ 1 * a01852 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a00155 ^ 1 * a03819 ^ 1)
theorem ha12785 : a12785.IsHomogeneous 181 := by
  unfold a12785
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01841.pow 1)).mul (ha01852.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12784 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12765 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12785 ^ 1)
theorem ha12786 : a12786.IsHomogeneous 188 := by
  unfold a12786
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12784.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12765.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12785.pow 1)))

@[irreducible]
def a12787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a07120 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00785 ^ 1 * a03803 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a03803 ^ 1)
theorem ha12787 : a12787.IsHomogeneous 194 := by
  unfold a12787
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha07120.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00785.pow 1)).mul (ha03803.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a12788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12787 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12784 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12766 ^ 1)
theorem ha12788 : a12788.IsHomogeneous 194 := by
  unfold a12788
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12787.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12784.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12766.pow 1)))

@[irreducible]
def a12789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12788 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12786 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12767 ^ 1)
theorem ha12789 : a12789.IsHomogeneous 194 := by
  unfold a12789
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12788.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12786.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12767.pow 1)))

@[irreducible]
def a12790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00155 ^ 1 * a03819 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a07143 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00289 ^ 1 * a03819 ^ 1)
theorem ha12790 : a12790.IsHomogeneous 174 := by
  unfold a12790
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha03819.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha07143.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12785 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12771 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12790 ^ 1)
theorem ha12791 : a12791.IsHomogeneous 181 := by
  unfold a12791
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12785.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12771.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12790.pow 1)))

@[irreducible]
def a12792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12786 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12772 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a12791 ^ 1)
theorem ha12792 : a12792.IsHomogeneous 188 := by
  unfold a12792
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12786.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12772.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha12791.pow 1)))

@[irreducible]
def a12793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12789 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12792 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12773 ^ 1)
theorem ha12793 : a12793.IsHomogeneous 194 := by
  unfold a12793
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12789.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12792.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12773.pow 1)))

@[irreducible]
def a12794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03800 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01839 ^ 1)
theorem ha12794 : a12794.IsHomogeneous 12 := by
  unfold a12794
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03800.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01839.pow 1)))

@[irreducible]
def a12795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01839 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha12795 : a12795.IsHomogeneous 6 := by
  unfold a12795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a12796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12794 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12795 ^ 1)
theorem ha12796 : a12796.IsHomogeneous 12 := by
  unfold a12796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12794.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12795.pow 1)))

@[irreducible]
def a12797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07116 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03800 ^ 1)
theorem ha12797 : a12797.IsHomogeneous 18 := by
  unfold a12797
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07116.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03800.pow 1)))

@[irreducible]
def a12798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12797 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12794 ^ 1)
theorem ha12798 : a12798.IsHomogeneous 18 := by
  unfold a12798
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12797.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12794.pow 1)))

@[irreducible]
def a12799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12798 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12796 ^ 1)
theorem ha12799 : a12799.IsHomogeneous 18 := by
  unfold a12799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12798.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12796.pow 1)))

end CycleQ2Concrete
