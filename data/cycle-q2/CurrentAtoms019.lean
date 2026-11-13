import Proposal.CurrentAtoms018

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a06656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06653 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06654 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06655 ^ 1)
theorem ha06656 : a06656.IsHomogeneous 30 := by
  unfold a06656
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06653.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06654.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06655.pow 1)))

@[irreducible]
def a06657 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00506 ^ 1) + (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a00506 ^ 1)
theorem ha06657 : a06657.IsHomogeneous 30 := by
  unfold a06657
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06658 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a02935 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a01327 ^ 1)
theorem ha06658 : a06658.IsHomogeneous 24 := by
  unfold a06658
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06659 : Poly := (C ((-5 : ℂ) / (168 : ℂ)) * a00003 ^ 6 * a06658 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06653 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06657 ^ 1)
theorem ha06659 : a06659.IsHomogeneous 30 := by
  unfold a06659
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (168 : ℂ))).mul (ha00003.pow 6)).mul (ha06658.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06653.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06657.pow 1)))

@[irreducible]
def a06660 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00506 ^ 1)
theorem ha06660 : a06660.IsHomogeneous 24 := by
  unfold a06660
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06661 : Poly := (C ((-5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06654 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a06657 ^ 1)
theorem ha06661 : a06661.IsHomogeneous 30 := by
  unfold a06661
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06654.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha06657.pow 1)))

@[irreducible]
def a06662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06656 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06659 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06661 ^ 1)
theorem ha06662 : a06662.IsHomogeneous 30 := by
  unfold a06662
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06659.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06661.pow 1)))

@[irreducible]
def a06663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00632 ^ 1)
theorem ha06663 : a06663.IsHomogeneous 24 := by
  unfold a06663
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a06664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00207 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00632 ^ 1)
theorem ha06664 : a06664.IsHomogeneous 18 := by
  unfold a06664
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a06665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06654 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06664 ^ 1)
theorem ha06665 : a06665.IsHomogeneous 30 := by
  unfold a06665
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06663.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06654.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06664.pow 1)))

@[irreducible]
def a06666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a01575 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha06666 : a06666.IsHomogeneous 18 := by
  unfold a06666
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01575.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06655 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06666 ^ 1)
theorem ha06667 : a06667.IsHomogeneous 30 := by
  unfold a06667
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06663.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06655.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06666.pow 1)))

@[irreducible]
def a06668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06656 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06665 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06667 ^ 1)
theorem ha06668 : a06668.IsHomogeneous 30 := by
  unfold a06668
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06665.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06667.pow 1)))

@[irreducible]
def a06669 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1)
theorem ha06669 : a06669.IsHomogeneous 18 := by
  unfold a06669
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a06670 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a06669 ^ 1) + (C ((-5 : ℂ) / (24 : ℂ)) * a06660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06664 ^ 1)
theorem ha06670 : a06670.IsHomogeneous 24 := by
  unfold a06670
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha06669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha06660.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06664.pow 1)))

@[irreducible]
def a06671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06661 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06665 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06670 ^ 1)
theorem ha06671 : a06671.IsHomogeneous 30 := by
  unfold a06671
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06661.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06665.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06670.pow 1)))

@[irreducible]
def a06672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06668 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06671 ^ 1)
theorem ha06672 : a06672.IsHomogeneous 30 := by
  unfold a06672
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06668.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06671.pow 1)))

@[irreducible]
def a06673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00632 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00506 ^ 1 * a01575 ^ 1)
theorem ha06673 : a06673.IsHomogeneous 30 := by
  unfold a06673
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a01327 ^ 1)
theorem ha06674 : a06674.IsHomogeneous 24 := by
  unfold a06674
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06653 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06673 ^ 1) + (C ((5 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a06674 ^ 1)
theorem ha06675 : a06675.IsHomogeneous 30 := by
  unfold a06675
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06653.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06673.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha06674.pow 1)))

@[irreducible]
def a06676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a01575 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a01575 ^ 1)
theorem ha06676 : a06676.IsHomogeneous 24 := by
  unfold a06676
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06655 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06673 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06676 ^ 1)
theorem ha06677 : a06677.IsHomogeneous 30 := by
  unfold a06677
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06673.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06676.pow 1)))

@[irreducible]
def a06678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06656 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06675 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06677 ^ 1)
theorem ha06678 : a06678.IsHomogeneous 30 := by
  unfold a06678
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06656.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06675.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06677.pow 1)))

@[irreducible]
def a06679 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a02935 ^ 1)
theorem ha06679 : a06679.IsHomogeneous 24 := by
  unfold a06679
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha05754.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06680 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a06674 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06658 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06679 ^ 1)
theorem ha06680 : a06680.IsHomogeneous 24 := by
  unfold a06680
  exact ((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha06674.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06658.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06679.pow 1)))

@[irreducible]
def a06681 : Poly := (C ((-5 : ℂ) / (168 : ℂ)) * a00003 ^ 6 * a06680 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06659 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06675 ^ 1)
theorem ha06681 : a06681.IsHomogeneous 30 := by
  unfold a06681
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (168 : ℂ))).mul (ha00003.pow 6)).mul (ha06680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06659.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06675.pow 1)))

@[irreducible]
def a06682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06681 ^ 1)
theorem ha06682 : a06682.IsHomogeneous 30 := by
  unfold a06682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06662.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06678.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06681.pow 1)))

@[irreducible]
def a06683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06426 ^ 1)
theorem ha06683 : a06683.IsHomogeneous 18 := by
  unfold a06683
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06426.pow 1)))

@[irreducible]
def a06684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06666 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a06683 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06676 ^ 1)
theorem ha06684 : a06684.IsHomogeneous 24 := by
  unfold a06684
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06666.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha06683.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06676.pow 1)))

@[irreducible]
def a06685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06677 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06684 ^ 1)
theorem ha06685 : a06685.IsHomogeneous 30 := by
  unfold a06685
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06677.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06684.pow 1)))

@[irreducible]
def a06686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06678 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a06685 ^ 1)
theorem ha06686 : a06686.IsHomogeneous 30 := by
  unfold a06686
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06678.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha06685.pow 1)))

@[irreducible]
def a06687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06682 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06686 ^ 1)
theorem ha06687 : a06687.IsHomogeneous 30 := by
  unfold a06687
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06682.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06686.pow 1)))

@[irreducible]
def a06688 : Poly := (C ((-2 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06652 ^ 1)
theorem ha06688 : a06688.IsHomogeneous 45 := by
  unfold a06688
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06652.pow 1)))

@[irreducible]
def a06689 : Poly := (C ((-2 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06652 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06688 ^ 1)
theorem ha06689 : a06689.IsHomogeneous 45 := by
  unfold a06689
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06652.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06688.pow 1)))

@[irreducible]
def a06690 : Poly := (C ((-4 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06688 ^ 1)
theorem ha06690 : a06690.IsHomogeneous 45 := by
  unfold a06690
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06688.pow 1)))

@[irreducible]
def a06691 : Poly := (C ((-2 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06689 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06690 ^ 1)
theorem ha06691 : a06691.IsHomogeneous 45 := by
  unfold a06691
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06689.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06690.pow 1)))

@[irreducible]
def a06692 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a06617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06539 ^ 1) + (C ((14 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06691 ^ 1)
theorem ha06692 : a06692.IsHomogeneous 50 := by
  unfold a06692
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha06617.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06539.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06691.pow 1)))

@[irreducible]
def a06693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a01617 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00655 ^ 1 * a00864 ^ 1)
theorem ha06693 : a06693.IsHomogeneous 45 := by
  unfold a06693
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00655.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a00864 ^ 1)
theorem ha06694 : a06694.IsHomogeneous 48 := by
  unfold a06694
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06694 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06693 ^ 1)
theorem ha06695 : a06695.IsHomogeneous 48 := by
  unfold a06695
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06694.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06693.pow 1)))

@[irreducible]
def a06696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01617 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03432 ^ 1)
theorem ha06696 : a06696.IsHomogeneous 39 := by
  unfold a06696
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a06697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06696 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06693 ^ 1)
theorem ha06697 : a06697.IsHomogeneous 45 := by
  unfold a06697
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06696.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06693.pow 1)))

@[irreducible]
def a06698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06695 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06697 ^ 1)
theorem ha06698 : a06698.IsHomogeneous 48 := by
  unfold a06698
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06695.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06697.pow 1)))

@[irreducible]
def a06699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a04085 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a02007 ^ 1)
theorem ha06699 : a06699.IsHomogeneous 48 := by
  unfold a06699
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a06700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06694 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06699 ^ 1)
theorem ha06700 : a06700.IsHomogeneous 48 := by
  unfold a06700
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06699.pow 1)))

@[irreducible]
def a06701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06695 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06700 ^ 1)
theorem ha06701 : a06701.IsHomogeneous 48 := by
  unfold a06701
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06700.pow 1)))

@[irreducible]
def a06702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06698 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06701 ^ 1)
theorem ha06702 : a06702.IsHomogeneous 48 := by
  unfold a06702
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06698.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06701.pow 1)))

@[irreducible]
def a06703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06529 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03432 ^ 1)
theorem ha06703 : a06703.IsHomogeneous 36 := by
  unfold a06703
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06529.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03432.pow 1)))

@[irreducible]
def a06704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06703 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06696 ^ 1)
theorem ha06704 : a06704.IsHomogeneous 42 := by
  unfold a06704
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06703.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06696.pow 1)))

@[irreducible]
def a06705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06704 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06697 ^ 1)
theorem ha06705 : a06705.IsHomogeneous 48 := by
  unfold a06705
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06704.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06697.pow 1)))

@[irreducible]
def a06706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06698 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a06705 ^ 1)
theorem ha06706 : a06706.IsHomogeneous 48 := by
  unfold a06706
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06698.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha06705.pow 1)))

@[irreducible]
def a06707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06706 ^ 1)
theorem ha06707 : a06707.IsHomogeneous 48 := by
  unfold a06707
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06706.pow 1)))

@[irreducible]
def a06708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06283 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a06707 ^ 1)
theorem ha06708 : a06708.IsHomogeneous 48 := by
  unfold a06708
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha06707.pow 1)))

@[irreducible]
def a06709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06708 ^ 1)
theorem ha06709 : a06709.IsHomogeneous 48 := by
  unfold a06709
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06708.pow 1)))

@[irreducible]
def a06710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06709 ^ 1)
theorem ha06710 : a06710.IsHomogeneous 48 := by
  unfold a06710
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06709.pow 1)))

@[irreducible]
def a06711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06707 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a06708 ^ 1)
theorem ha06711 : a06711.IsHomogeneous 48 := by
  unfold a06711
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha06708.pow 1)))

@[irreducible]
def a06712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06709 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a06711 ^ 1)
theorem ha06712 : a06712.IsHomogeneous 48 := by
  unfold a06712
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06709.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha06711.pow 1)))

@[irreducible]
def a06713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06710 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06712 ^ 1)
theorem ha06713 : a06713.IsHomogeneous 48 := by
  unfold a06713
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06710.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06712.pow 1)))

@[irreducible]
def a06714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06710 ^ 1)
theorem ha06714 : a06714.IsHomogeneous 48 := by
  unfold a06714
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06710.pow 1)))

@[irreducible]
def a06715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06714 ^ 1)
theorem ha06715 : a06715.IsHomogeneous 48 := by
  unfold a06715
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06714.pow 1)))

@[irreducible]
def a06716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06323 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06381 ^ 1)
theorem ha06716 : a06716.IsHomogeneous 48 := by
  unfold a06716
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06381.pow 1)))

@[irreducible]
def a06717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06323 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06716 ^ 1)
theorem ha06717 : a06717.IsHomogeneous 48 := by
  unfold a06717
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06716.pow 1)))

@[irreducible]
def a06718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06323 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06717 ^ 1)
theorem ha06718 : a06718.IsHomogeneous 48 := by
  unfold a06718
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06717.pow 1)))

@[irreducible]
def a06719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06381 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06716 ^ 1)
theorem ha06719 : a06719.IsHomogeneous 48 := by
  unfold a06719
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06716.pow 1)))

@[irreducible]
def a06720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06717 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06719 ^ 1)
theorem ha06720 : a06720.IsHomogeneous 48 := by
  unfold a06720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06719.pow 1)))

@[irreducible]
def a06721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06718 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06720 ^ 1)
theorem ha06721 : a06721.IsHomogeneous 48 := by
  unfold a06721
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06720.pow 1)))

@[irreducible]
def a06722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06719 ^ 1)
theorem ha06722 : a06722.IsHomogeneous 48 := by
  unfold a06722
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06719.pow 1)))

@[irreducible]
def a06723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06720 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06722 ^ 1)
theorem ha06723 : a06723.IsHomogeneous 48 := by
  unfold a06723
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06720.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06722.pow 1)))

@[irreducible]
def a06724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06723 ^ 1)
theorem ha06724 : a06724.IsHomogeneous 48 := by
  unfold a06724
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06723.pow 1)))

@[irreducible]
def a06725 : Poly := (C ((-70 : ℂ) / (81 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06431 ^ 1) + (C ((-2 : ℂ) / (9 : ℂ)) * a06724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06715 ^ 1)
theorem ha06725 : a06725.IsHomogeneous 48 := by
  unfold a06725
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-70 : ℂ) / (81 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha06724.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06715.pow 1)))

@[irreducible]
def a06726 : Poly := (C ((-27 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00003 ^ 2 * a00012 ^ 5 * a00014 ^ 1 * a05840 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a06253 ^ 1) + (C ((-1 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a06434 ^ 1) + (C ((-1 : ℂ) / (15360 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00003 ^ 2 * a00004 ^ 6 * a00005 ^ 6 * a06725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a06050 ^ 1) + (C ((1 : ℂ) / (3072 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00003 ^ 1 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a06692 ^ 1)
theorem ha06726 : a06726.IsHomogeneous 87 := by
  unfold a06726
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 5)).mul (ha00014.pow 1)).mul (ha05840.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha06253.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha06434.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15360 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha06725.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha06050.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3072 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00003.pow 1)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha06692.pow 1)))

@[irreducible]
def a06727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a06726 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a03563 ^ 1)
theorem ha06727 : a06727.IsHomogeneous 173 := by
  unfold a06727
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha06726.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha03563.pow 1)))

@[irreducible]
def a06728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06727 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a05739 ^ 1)
theorem ha06728 : a06728.IsHomogeneous 179 := by
  unfold a06728
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha05739.pow 1)))

@[irreducible]
def a06729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05740 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a06728 ^ 1)
theorem ha06729 : a06729.IsHomogeneous 179 := by
  unfold a06729
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha06728.pow 1)))

@[irreducible]
def a06730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05740 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06729 ^ 1)
theorem ha06730 : a06730.IsHomogeneous 179 := by
  unfold a06730
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06729.pow 1)))

@[irreducible]
def a06731 : Poly := (C ((-5 : ℂ) / (64 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a06730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a03566 ^ 1)
theorem ha06731 : a06731.IsHomogeneous 265 := by
  unfold a06731
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (64 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha06730.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha03566.pow 1)))

@[irreducible]
def a06732 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a06731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05724 ^ 1)
theorem ha06732 : a06732.IsHomogeneous 345 := by
  unfold a06732
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha06731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05724.pow 1)))

@[irreducible]
def a06733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05725 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a06732 ^ 1)
theorem ha06733 : a06733.IsHomogeneous 425 := by
  unfold a06733
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05725.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha06732.pow 1)))

@[irreducible]
def a06734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06733 ^ 1)
theorem ha06734 : a06734.IsHomogeneous 425 := by
  unfold a06734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06733.pow 1)))

@[irreducible]
def a06735 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00295 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a06734 ^ 1)
theorem ha06735 : a06735.IsHomogeneous 808 := by
  unfold a06735
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00295.pow 1)).mul (ha03569.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha06734.pow 1)))

@[irreducible]
def a06736 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05718 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06735 ^ 1)
theorem ha06736 : a06736.IsHomogeneous 1062 := by
  unfold a06736
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05718.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06735.pow 1)))

@[irreducible]
def a06737 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06736 ^ 1)
theorem ha06737 : a06737.IsHomogeneous 1316 := by
  unfold a06737
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05719.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06736.pow 1)))

@[irreducible]
def a06738 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05722 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06737 ^ 1)
theorem ha06738 : a06738.IsHomogeneous 1570 := by
  unfold a06738
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05722.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06737.pow 1)))

@[irreducible]
def a06739 : Poly := (C ((-108 : ℂ) / (5 : ℂ)) * a00800 ^ 1 * a01871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a01880 ^ 1)
theorem ha06739 : a06739.IsHomogeneous 921 := by
  unfold a06739
  exact ((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (5 : ℂ))).mul (ha00800.pow 1)).mul (ha01871.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha01880.pow 1)))

@[irreducible]
def a06740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00294 ^ 1 * a03851 ^ 1) + (C ((3 : ℂ) / (32 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00800 ^ 1 * a01871 ^ 1)
theorem ha06740 : a06740.IsHomogeneous 1175 := by
  unfold a06740
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00294.pow 1)).mul (ha03851.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (32 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00800.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a06741 : Poly := (C ((-5 : ℂ) / (1152 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06740 ^ 1)
theorem ha06741 : a06741.IsHomogeneous 1175 := by
  unfold a06741
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1152 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06740.pow 1)))

@[irreducible]
def a06742 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a03865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a01880 ^ 1)
theorem ha06742 : a06742.IsHomogeneous 666 := by
  unfold a06742
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha03865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha01880.pow 1)))

@[irreducible]
def a06743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06739 ^ 1)
theorem ha06743 : a06743.IsHomogeneous 921 := by
  unfold a06743
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06742.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06739.pow 1)))

@[irreducible]
def a06744 : Poly := (C ((-5 : ℂ) / (1152 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06741 ^ 1)
theorem ha06744 : a06744.IsHomogeneous 1175 := by
  unfold a06744
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1152 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06741.pow 1)))

@[irreducible]
def a06745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00793 ^ 1 * a01830 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00778 ^ 1 * a01868 ^ 1)
theorem ha06745 : a06745.IsHomogeneous 1120 := by
  unfold a06745
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00793.pow 1)).mul (ha01830.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00778.pow 1)).mul (ha01868.pow 1)))

@[irreducible]
def a06746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a03775 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00793 ^ 1 * a01830 ^ 1)
theorem ha06746 : a06746.IsHomogeneous 1102 := by
  unfold a06746
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha03775.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00793.pow 1)).mul (ha01830.pow 1)))

@[irreducible]
def a06747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06746 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a06745 ^ 1)
theorem ha06747 : a06747.IsHomogeneous 1162 := by
  unfold a06747
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06746.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha06745.pow 1)))

@[irreducible]
def a06748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00778 ^ 1 * a01868 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00287 ^ 1 * a03847 ^ 1)
theorem ha06748 : a06748.IsHomogeneous 1138 := by
  unfold a06748
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00778.pow 1)).mul (ha01868.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00287.pow 1)).mul (ha03847.pow 1)))

@[irreducible]
def a06749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06745 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a06748 ^ 1)
theorem ha06749 : a06749.IsHomogeneous 1180 := by
  unfold a06749
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06745.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha06748.pow 1)))

@[irreducible]
def a06750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06747 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a06749 ^ 1)
theorem ha06750 : a06750.IsHomogeneous 1222 := by
  unfold a06750
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06747.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha06749.pow 1)))

@[irreducible]
def a06751 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00776 ^ 1 * a01739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00734 ^ 1 * a01827 ^ 1)
theorem ha06751 : a06751.IsHomogeneous 624 := by
  unfold a06751
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00776.pow 1)).mul (ha01739.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00734.pow 1)).mul (ha01827.pow 1)))

@[irreducible]
def a06752 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a03612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00776 ^ 1 * a01739 ^ 1)
theorem ha06752 : a06752.IsHomogeneous 479 := by
  unfold a06752
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha03612.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00776.pow 1)).mul (ha01739.pow 1)))

@[irreducible]
def a06753 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06752 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06751 ^ 1)
theorem ha06753 : a06753.IsHomogeneous 624 := by
  unfold a06753
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06752.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06751.pow 1)))

@[irreducible]
def a06754 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00734 ^ 1 * a01827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00271 ^ 1 * a03771 ^ 1)
theorem ha06754 : a06754.IsHomogeneous 714 := by
  unfold a06754
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00734.pow 1)).mul (ha01827.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00271.pow 1)).mul (ha03771.pow 1)))

@[irreducible]
def a06755 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06751 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a06754 ^ 1)
theorem ha06755 : a06755.IsHomogeneous 769 := by
  unfold a06755
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06751.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha06754.pow 1)))

@[irreducible]
def a06756 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06753 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06755 ^ 1)
theorem ha06756 : a06756.IsHomogeneous 769 := by
  unfold a06756
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06755.pow 1)))

@[irreducible]
def a06757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00724 ^ 1 * a01736 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00732 ^ 1 * a01726 ^ 1)
theorem ha06757 : a06757.IsHomogeneous 187 := by
  unfold a06757
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00724.pow 1)).mul (ha01736.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00732.pow 1)).mul (ha01726.pow 1)))

@[irreducible]
def a06758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00732 ^ 1 * a01726 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00270 ^ 1 * a03604 ^ 1)
theorem ha06758 : a06758.IsHomogeneous 188 := by
  unfold a06758
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00732.pow 1)).mul (ha01726.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00270.pow 1)).mul (ha03604.pow 1)))

@[irreducible]
def a06759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06757 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a06758 ^ 1)
theorem ha06759 : a06759.IsHomogeneous 188 := by
  unfold a06759
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha06758.pow 1)))

@[irreducible]
def a06760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00724 ^ 1 * a01736 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a00265 ^ 1 * a03608 ^ 1)
theorem ha06760 : a06760.IsHomogeneous 132 := by
  unfold a06760
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00724.pow 1)).mul (ha01736.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha03608.pow 1)))

@[irreducible]
def a06761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a06760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06757 ^ 1)
theorem ha06761 : a06761.IsHomogeneous 187 := by
  unfold a06761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha06760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06757.pow 1)))

@[irreducible]
def a06762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06759 ^ 1)
theorem ha06762 : a06762.IsHomogeneous 188 := by
  unfold a06762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06761.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06759.pow 1)))

@[irreducible]
def a06763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00723 ^ 1 * a01852 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00785 ^ 1 * a01724 ^ 1)
theorem ha06763 : a06763.IsHomogeneous 163 := by
  unfold a06763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00723.pow 1)).mul (ha01852.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00785.pow 1)).mul (ha01724.pow 1)))

@[irreducible]
def a06764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a03601 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00785 ^ 1 * a01724 ^ 1)
theorem ha06764 : a06764.IsHomogeneous 163 := by
  unfold a06764
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha03601.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00785.pow 1)).mul (ha01724.pow 1)))

@[irreducible]
def a06765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06763 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06764 ^ 1)
theorem ha06765 : a06765.IsHomogeneous 163 := by
  unfold a06765
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06764.pow 1)))

@[irreducible]
def a06766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a03819 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00723 ^ 1 * a01852 ^ 1)
theorem ha06766 : a06766.IsHomogeneous 163 := by
  unfold a06766
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha03819.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00723.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a06767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06763 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06766 ^ 1)
theorem ha06767 : a06767.IsHomogeneous 163 := by
  unfold a06767
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06766.pow 1)))

@[irreducible]
def a06768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06765 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06767 ^ 1)
theorem ha06768 : a06768.IsHomogeneous 163 := by
  unfold a06768
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06767.pow 1)))

@[irreducible]
def a06769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a03590 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01716 ^ 1)
theorem ha06769 : a06769.IsHomogeneous 42 := by
  unfold a06769
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha03590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01716.pow 1)))

@[irreducible]
def a06770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06769 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 2 * a03714 ^ 1)
theorem ha06770 : a06770.IsHomogeneous 42 := by
  unfold a06770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06769.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 2)).mul (ha03714.pow 1)))

@[irreducible]
def a06771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06770 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a03715 ^ 1)
theorem ha06771 : a06771.IsHomogeneous 42 := by
  unfold a06771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06770.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha03715.pow 1)))

@[irreducible]
def a06772 : Poly := (C ((-7 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 3) + (C ((-1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a05754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1 * a04085 ^ 1)
theorem ha06772 : a06772.IsHomogeneous 36 := by
  unfold a06772
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha05754.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a06773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a06772 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a03590 ^ 1)
theorem ha06773 : a06773.IsHomogeneous 42 := by
  unfold a06773
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a06774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06769 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06773 ^ 1)
theorem ha06774 : a06774.IsHomogeneous 42 := by
  unfold a06774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06773.pow 1)))

@[irreducible]
def a06775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06774 ^ 1)
theorem ha06775 : a06775.IsHomogeneous 42 := by
  unfold a06775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06774.pow 1)))

@[irreducible]
def a06776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06775 ^ 1)
theorem ha06776 : a06776.IsHomogeneous 42 := by
  unfold a06776
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06775.pow 1)))

@[irreducible]
def a06777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03716 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a06771 ^ 1)
theorem ha06777 : a06777.IsHomogeneous 42 := by
  unfold a06777
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha06771.pow 1)))

@[irreducible]
def a06778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06776 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a06777 ^ 1)
theorem ha06778 : a06778.IsHomogeneous 42 := by
  unfold a06778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06776.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha06777.pow 1)))

@[irreducible]
def a06779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a03597 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a01721 ^ 1)
theorem ha06779 : a06779.IsHomogeneous 44 := by
  unfold a06779
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha03597.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a06780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06779 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a01721 ^ 1)
theorem ha06780 : a06780.IsHomogeneous 44 := by
  unfold a06780
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a06781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a05775 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1)
theorem ha06781 : a06781.IsHomogeneous 19 := by
  unfold a06781
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha05775.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a06782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a06781 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a03597 ^ 1)
theorem ha06782 : a06782.IsHomogeneous 44 := by
  unfold a06782
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha03597.pow 1)))

@[irreducible]
def a06783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06779 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06782 ^ 1)
theorem ha06783 : a06783.IsHomogeneous 44 := by
  unfold a06783
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06779.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06782.pow 1)))

@[irreducible]
def a06784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06780 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06783 ^ 1)
theorem ha06784 : a06784.IsHomogeneous 44 := by
  unfold a06784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06780.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06783.pow 1)))

@[irreducible]
def a06785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06780 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06784 ^ 1)
theorem ha06785 : a06785.IsHomogeneous 44 := by
  unfold a06785
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06780.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06784.pow 1)))

@[irreducible]
def a06786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a06785 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a06778 ^ 1)
theorem ha06786 : a06786.IsHomogeneous 49 := by
  unfold a06786
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha06785.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha06778.pow 1)))

@[irreducible]
def a06787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a03601 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00105 ^ 1 * a06786 ^ 1)
theorem ha06787 : a06787.IsHomogeneous 107 := by
  unfold a06787
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha03601.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00105.pow 1)).mul (ha06786.pow 1)))

@[irreducible]
def a06788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a06787 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06764 ^ 1)
theorem ha06788 : a06788.IsHomogeneous 163 := by
  unfold a06788
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha06787.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06764.pow 1)))

@[irreducible]
def a06789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06765 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06788 ^ 1)
theorem ha06789 : a06789.IsHomogeneous 163 := by
  unfold a06789
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06788.pow 1)))

@[irreducible]
def a06790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06789 ^ 1)
theorem ha06790 : a06790.IsHomogeneous 163 := by
  unfold a06790
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06789.pow 1)))

@[irreducible]
def a06791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00117 ^ 1 * a06790 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00270 ^ 1 * a03604 ^ 1)
theorem ha06791 : a06791.IsHomogeneous 188 := by
  unfold a06791
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00117.pow 1)).mul (ha06790.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00270.pow 1)).mul (ha03604.pow 1)))

@[irreducible]
def a06792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06758 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a06791 ^ 1)
theorem ha06792 : a06792.IsHomogeneous 188 := by
  unfold a06792
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06758.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha06791.pow 1)))

@[irreducible]
def a06793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06759 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a06792 ^ 1)
theorem ha06793 : a06793.IsHomogeneous 188 := by
  unfold a06793
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06759.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha06792.pow 1)))

@[irreducible]
def a06794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06793 ^ 1)
theorem ha06794 : a06794.IsHomogeneous 188 := by
  unfold a06794
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06762.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06793.pow 1)))

@[irreducible]
def a06795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00105 ^ 1)
theorem ha06795 : a06795.IsHomogeneous 55 := by
  unfold a06795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00105.pow 1)))

@[irreducible]
def a06796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06760 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a03608 ^ 1 * a06795 ^ 1)
theorem ha06796 : a06796.IsHomogeneous 132 := by
  unfold a06796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06760.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha03608.pow 1)).mul (ha06795.pow 1)))

@[irreducible]
def a06797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a06796 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06761 ^ 1)
theorem ha06797 : a06797.IsHomogeneous 187 := by
  unfold a06797
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha06796.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06761.pow 1)))

@[irreducible]
def a06798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06797 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06762 ^ 1)
theorem ha06798 : a06798.IsHomogeneous 188 := by
  unfold a06798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06762.pow 1)))

@[irreducible]
def a06799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06794 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06798 ^ 1)
theorem ha06799 : a06799.IsHomogeneous 188 := by
  unfold a06799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06794.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06798.pow 1)))

@[irreducible]
def a06800 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a03612 ^ 1)
theorem ha06800 : a06800.IsHomogeneous 334 := by
  unfold a06800
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06799.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha03612.pow 1)))

@[irreducible]
def a06801 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06800 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06752 ^ 1)
theorem ha06801 : a06801.IsHomogeneous 479 := by
  unfold a06801
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06800.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06752.pow 1)))

@[irreducible]
def a06802 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06753 ^ 1)
theorem ha06802 : a06802.IsHomogeneous 624 := by
  unfold a06802
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06801.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06753.pow 1)))

@[irreducible]
def a06803 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06756 ^ 1)
theorem ha06803 : a06803.IsHomogeneous 769 := by
  unfold a06803
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06802.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06756.pow 1)))

@[irreducible]
def a06804 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01742 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a03620 ^ 1)
theorem ha06804 : a06804.IsHomogeneous 621 := by
  unfold a06804
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01742.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha03620.pow 1)))

@[irreducible]
def a06805 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01742 ^ 1 * a01825 ^ 1)
theorem ha06805 : a06805.IsHomogeneous 475 := by
  unfold a06805
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01742.pow 1)).mul (ha01825.pow 1)))

@[irreducible]
def a06806 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06804 ^ 1)
theorem ha06806 : a06806.IsHomogeneous 621 := by
  unfold a06806
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06805.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06804.pow 1)))

@[irreducible]
def a06807 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a03617 ^ 1)
theorem ha06807 : a06807.IsHomogeneous 476 := by
  unfold a06807
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha03617.pow 1)))

@[irreducible]
def a06808 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a00775 ^ 1)
theorem ha06808 : a06808.IsHomogeneous 331 := by
  unfold a06808
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha00775.pow 1)))

@[irreducible]
def a06809 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 2)
theorem ha06809 : a06809.IsHomogeneous 290 := by
  unfold a06809
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 2)))

@[irreducible]
def a06810 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06809 ^ 1)
theorem ha06810 : a06810.IsHomogeneous 290 := by
  unfold a06810
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06809.pow 1)))

@[irreducible]
def a06811 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06808 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a06810 ^ 1)
theorem ha06811 : a06811.IsHomogeneous 435 := by
  unfold a06811
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06808.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha06810.pow 1)))

@[irreducible]
def a06812 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a03617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a06811 ^ 1)
theorem ha06812 : a06812.IsHomogeneous 580 := by
  unfold a06812
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha03617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha06811.pow 1)))

@[irreducible]
def a06813 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06807 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06812 ^ 1)
theorem ha06813 : a06813.IsHomogeneous 580 := by
  unfold a06813
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06807.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06812.pow 1)))

@[irreducible]
def a06814 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a01825 ^ 1)
theorem ha06814 : a06814.IsHomogeneous 330 := by
  unfold a06814
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha01825.pow 1)))

@[irreducible]
def a06815 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06814 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06807 ^ 1)
theorem ha06815 : a06815.IsHomogeneous 476 := by
  unfold a06815
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06814.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06807.pow 1)))

@[irreducible]
def a06816 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06815 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06813 ^ 1)
theorem ha06816 : a06816.IsHomogeneous 580 := by
  unfold a06816
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06813.pow 1)))

@[irreducible]
def a06817 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a03620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a06816 ^ 1)
theorem ha06817 : a06817.IsHomogeneous 725 := by
  unfold a06817
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha03620.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha06816.pow 1)))

@[irreducible]
def a06818 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06817 ^ 1)
theorem ha06818 : a06818.IsHomogeneous 725 := by
  unfold a06818
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06804.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06817.pow 1)))

@[irreducible]
def a06819 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06818 ^ 1)
theorem ha06819 : a06819.IsHomogeneous 725 := by
  unfold a06819
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06818.pow 1)))

@[irreducible]
def a06820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00285 ^ 1 * a00737 ^ 1)
theorem ha06820 : a06820.IsHomogeneous 179 := by
  unfold a06820
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a06821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00737 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01750 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00285 ^ 1 * a00737 ^ 1)
theorem ha06821 : a06821.IsHomogeneous 179 := by
  unfold a06821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01750.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a06822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a00262 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00737 ^ 1)
theorem ha06822 : a06822.IsHomogeneous 179 := by
  unfold a06822
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a06823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06821 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06822 ^ 1)
theorem ha06823 : a06823.IsHomogeneous 179 := by
  unfold a06823
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06821.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06822.pow 1)))

@[irreducible]
def a06824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00773 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00773 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a01822 ^ 1)
theorem ha06824 : a06824.IsHomogeneous 138 := by
  unfold a06824
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a06825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00773 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00285 ^ 1)
theorem ha06825 : a06825.IsHomogeneous 139 := by
  unfold a06825
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00285.pow 1)))

@[irreducible]
def a06826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a06825 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a06824 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06820 ^ 1)
theorem ha06826 : a06826.IsHomogeneous 181 := by
  unfold a06826
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha06825.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha06824.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06820.pow 1)))

@[irreducible]
def a06827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00123 ^ 1 * a00262 ^ 1)
theorem ha06827 : a06827.IsHomogeneous 139 := by
  unfold a06827
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00123.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a06828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a06825 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a06827 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06822 ^ 1)
theorem ha06828 : a06828.IsHomogeneous 181 := by
  unfold a06828
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha06825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha06827.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06822.pow 1)))

@[irreducible]
def a06829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06826 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06828 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06823 ^ 1)
theorem ha06829 : a06829.IsHomogeneous 181 := by
  unfold a06829
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06826.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06828.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06823.pow 1)))

@[irreducible]
def a06830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00737 ^ 1 * a00773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00737 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00285 ^ 1 * a01750 ^ 1)
theorem ha06830 : a06830.IsHomogeneous 179 := by
  unfold a06830
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00737.pow 1)).mul (ha00773.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00285.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a06831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00737 ^ 1 * a00773 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a01822 ^ 1)
theorem ha06831 : a06831.IsHomogeneous 178 := by
  unfold a06831
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00737.pow 1)).mul (ha00773.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a06832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06820 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a06831 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a06830 ^ 1)
theorem ha06832 : a06832.IsHomogeneous 179 := by
  unfold a06832
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06820.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha06831.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha06830.pow 1)))

@[irreducible]
def a06833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a01750 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03639 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a01750 ^ 1)
theorem ha06833 : a06833.IsHomogeneous 178 := by
  unfold a06833
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha01750.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03639.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a06834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06821 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a06833 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a06830 ^ 1)
theorem ha06834 : a06834.IsHomogeneous 179 := by
  unfold a06834
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06821.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha06833.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha06830.pow 1)))

@[irreducible]
def a06835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06832 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06834 ^ 1)
theorem ha06835 : a06835.IsHomogeneous 179 := by
  unfold a06835
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06823.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06832.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06834.pow 1)))

@[irreducible]
def a06836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a03764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01822 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a01822 ^ 1)
theorem ha06836 : a06836.IsHomogeneous 137 := by
  unfold a06836
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha03764.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01822.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a06837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a06824 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06831 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a06836 ^ 1)
theorem ha06837 : a06837.IsHomogeneous 180 := by
  unfold a06837
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha06824.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06831.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha06836.pow 1)))

@[irreducible]
def a06838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06826 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a06837 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06832 ^ 1)
theorem ha06838 : a06838.IsHomogeneous 181 := by
  unfold a06838
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06826.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha06837.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06832.pow 1)))

@[irreducible]
def a06839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06838 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06835 ^ 1)
theorem ha06839 : a06839.IsHomogeneous 181 := by
  unfold a06839
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06838.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06835.pow 1)))

@[irreducible]
def a06840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00737 ^ 1 * a00773 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00773 ^ 1 * a01750 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a01822 ^ 1)
theorem ha06840 : a06840.IsHomogeneous 183 := by
  unfold a06840
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00737.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00773.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a06841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00285 ^ 1 * a01750 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a03639 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00773 ^ 1 * a01750 ^ 1)
theorem ha06841 : a06841.IsHomogeneous 183 := by
  unfold a06841
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00285.pow 1)).mul (ha01750.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha03639.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00773.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a06842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06840 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06841 ^ 1)
theorem ha06842 : a06842.IsHomogeneous 183 := by
  unfold a06842
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06830.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06840.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06841.pow 1)))

@[irreducible]
def a06843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a03764 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00262 ^ 1 * a01822 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a01822 ^ 1)
theorem ha06843 : a06843.IsHomogeneous 183 := by
  unfold a06843
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha03764.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a06844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a06831 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a06840 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a06843 ^ 1)
theorem ha06844 : a06844.IsHomogeneous 183 := by
  unfold a06844
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha06831.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha06840.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha06843.pow 1)))

@[irreducible]
def a06845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06832 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a06844 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a06842 ^ 1)
theorem ha06845 : a06845.IsHomogeneous 183 := by
  unfold a06845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06832.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha06844.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha06842.pow 1)))

@[irreducible]
def a06846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00262 ^ 1 * a03590 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00717 ^ 1 * a01716 ^ 1)
theorem ha06846 : a06846.IsHomogeneous 79 := by
  unfold a06846
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00262.pow 1)).mul (ha03590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00717.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a06847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (10 : ℂ)) * a06846 ^ 1)
theorem ha06847 : a06847.IsHomogeneous 79 := by
  unfold a06847
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)).mul (ha01716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (10 : ℂ))).mul (ha06846.pow 1)))

@[irreducible]
def a06848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a06772 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a03590 ^ 1)
theorem ha06848 : a06848.IsHomogeneous 78 := by
  unfold a06848
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a06849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06848 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a06846 ^ 1)
theorem ha06849 : a06849.IsHomogeneous 79 := by
  unfold a06849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06848.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha06846.pow 1)))

@[irreducible]
def a06850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06847 ^ 1) + (C ((1 : ℂ) / (30 : ℂ)) * a06849 ^ 1)
theorem ha06850 : a06850.IsHomogeneous 79 := by
  unfold a06850
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (30 : ℂ))).mul (ha06849.pow 1)))

@[irreducible]
def a06851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06847 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06850 ^ 1)
theorem ha06851 : a06851.IsHomogeneous 79 := by
  unfold a06851
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06850.pow 1)))

@[irreducible]
def a06852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a06851 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00123 ^ 1 * a03639 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a03639 ^ 1)
theorem ha06852 : a06852.IsHomogeneous 183 := by
  unfold a06852
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha06851.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00123.pow 1)).mul (ha03639.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha03639.pow 1)))

@[irreducible]
def a06853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a06833 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a06852 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a06841 ^ 1)
theorem ha06853 : a06853.IsHomogeneous 183 := by
  unfold a06853
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha06833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha06852.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha06841.pow 1)))

@[irreducible]
def a06854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06834 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06853 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a06842 ^ 1)
theorem ha06854 : a06854.IsHomogeneous 183 := by
  unfold a06854
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06834.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06853.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha06842.pow 1)))

@[irreducible]
def a06855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06845 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06854 ^ 1)
theorem ha06855 : a06855.IsHomogeneous 183 := by
  unfold a06855
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06835.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06845.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06854.pow 1)))

@[irreducible]
def a06856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00749 ^ 1 * a01779 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00751 ^ 1 * a01776 ^ 1)
theorem ha06856 : a06856.IsHomogeneous 88 := by
  unfold a06856
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00749.pow 1)).mul (ha01779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00751.pow 1)).mul (ha01776.pow 1)))

@[irreducible]
def a06857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00276 ^ 1 * a03686 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00751 ^ 1 * a01776 ^ 1)
theorem ha06857 : a06857.IsHomogeneous 88 := by
  unfold a06857
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00276.pow 1)).mul (ha03686.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00751.pow 1)).mul (ha01776.pow 1)))

@[irreducible]
def a06858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06857 ^ 1)
theorem ha06858 : a06858.IsHomogeneous 88 := by
  unfold a06858
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06857.pow 1)))

@[irreducible]
def a06859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00275 ^ 1 * a03690 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00749 ^ 1 * a01779 ^ 1)
theorem ha06859 : a06859.IsHomogeneous 88 := by
  unfold a06859
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00275.pow 1)).mul (ha03690.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00749.pow 1)).mul (ha01779.pow 1)))

@[irreducible]
def a06860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06856 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06859 ^ 1)
theorem ha06860 : a06860.IsHomogeneous 88 := by
  unfold a06860
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06859.pow 1)))

@[irreducible]
def a06861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06860 ^ 1)
theorem ha06861 : a06861.IsHomogeneous 88 := by
  unfold a06861
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06860.pow 1)))

@[irreducible]
def a06862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00262 ^ 1)
theorem ha06862 : a06862.IsHomogeneous 46 := by
  unfold a06862
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)))

@[irreducible]
def a06863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1)
theorem ha06863 : a06863.IsHomogeneous 46 := by
  unfold a06863
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00717 ^ 1)
theorem ha06864 : a06864.IsHomogeneous 46 := by
  unfold a06864
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06862 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06864 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06863 ^ 1)
theorem ha06865 : a06865.IsHomogeneous 46 := by
  unfold a06865
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06862.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06864.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06863.pow 1)))

@[irreducible]
def a06866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha06866 : a06866.IsHomogeneous 42 := by
  unfold a06866
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a06867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00103 ^ 1)
theorem ha06867 : a06867.IsHomogeneous 48 := by
  unfold a06867
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)))

@[irreducible]
def a06868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06867 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06862 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06866 ^ 1)
theorem ha06868 : a06868.IsHomogeneous 48 := by
  unfold a06868
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06867.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06862.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06866.pow 1)))

@[irreducible]
def a06869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1)
theorem ha06869 : a06869.IsHomogeneous 48 := by
  unfold a06869
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a06870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06867 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06869 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a06864 ^ 1)
theorem ha06870 : a06870.IsHomogeneous 48 := by
  unfold a06870
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06867.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06869.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha06864.pow 1)))

@[irreducible]
def a06871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06870 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06865 ^ 1)
theorem ha06871 : a06871.IsHomogeneous 48 := by
  unfold a06871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06870.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06865.pow 1)))

@[irreducible]
def a06872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a01716 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00717 ^ 1)
theorem ha06872 : a06872.IsHomogeneous 46 := by
  unfold a06872
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00717.pow 1)))

@[irreducible]
def a06873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00717 ^ 1)
theorem ha06873 : a06873.IsHomogeneous 40 := by
  unfold a06873
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a06874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06862 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a06872 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06873 ^ 1)
theorem ha06874 : a06874.IsHomogeneous 46 := by
  unfold a06874
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06862.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha06872.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06873.pow 1)))

@[irreducible]
def a06875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a03590 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a01716 ^ 1)
theorem ha06875 : a06875.IsHomogeneous 45 := by
  unfold a06875
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha03590.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a06876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06875 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06863 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06872 ^ 1)
theorem ha06876 : a06876.IsHomogeneous 46 := by
  unfold a06876
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06863.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06872.pow 1)))

@[irreducible]
def a06877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06874 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06876 ^ 1)
theorem ha06877 : a06877.IsHomogeneous 46 := by
  unfold a06877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06865.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06874.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06876.pow 1)))

@[irreducible]
def a06878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06866 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06873 ^ 1)
theorem ha06878 : a06878.IsHomogeneous 42 := by
  unfold a06878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06866.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06873.pow 1)))

@[irreducible]
def a06879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06868 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06874 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06878 ^ 1)
theorem ha06879 : a06879.IsHomogeneous 48 := by
  unfold a06879
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06868.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06874.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06878.pow 1)))

@[irreducible]
def a06880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06879 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06877 ^ 1)
theorem ha06880 : a06880.IsHomogeneous 48 := by
  unfold a06880
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06871.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06879.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06877.pow 1)))

@[irreducible]
def a06881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a01716 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00717 ^ 1)
theorem ha06881 : a06881.IsHomogeneous 46 := by
  unfold a06881
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha01716.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00717.pow 1)))

@[irreducible]
def a06882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a01716 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a01716 ^ 1)
theorem ha06882 : a06882.IsHomogeneous 48 := by
  unfold a06882
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha03590.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a06883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06882 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a06872 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 2 * a06881 ^ 1)
theorem ha06883 : a06883.IsHomogeneous 48 := by
  unfold a06883
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06882.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha06872.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 2)).mul (ha06881.pow 1)))

@[irreducible]
def a06884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00262 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00262 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00717 ^ 1)
theorem ha06884 : a06884.IsHomogeneous 46 := by
  unfold a06884
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06881 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06884 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06873 ^ 1)
theorem ha06885 : a06885.IsHomogeneous 46 := by
  unfold a06885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06881.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06884.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06873.pow 1)))

@[irreducible]
def a06886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06883 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06874 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 2 * a06885 ^ 1)
theorem ha06886 : a06886.IsHomogeneous 48 := by
  unfold a06886
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06874.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 2)).mul (ha06885.pow 1)))

@[irreducible]
def a06887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a06772 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a03590 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a03590 ^ 1)
theorem ha06887 : a06887.IsHomogeneous 48 := by
  unfold a06887
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a06888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06882 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06887 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06875 ^ 1)
theorem ha06888 : a06888.IsHomogeneous 48 := by
  unfold a06888
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06887.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06875.pow 1)))

@[irreducible]
def a06889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06888 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a06876 ^ 1)
theorem ha06889 : a06889.IsHomogeneous 48 := by
  unfold a06889
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06888.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha06876.pow 1)))

@[irreducible]
def a06890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06889 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06877 ^ 1)
theorem ha06890 : a06890.IsHomogeneous 48 := by
  unfold a06890
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06886.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06889.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06877.pow 1)))

@[irreducible]
def a06891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00009 ^ 1 * a00262 ^ 1)
theorem ha06891 : a06891.IsHomogeneous 48 := by
  unfold a06891
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a06892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06891 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06884 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06866 ^ 1)
theorem ha06892 : a06892.IsHomogeneous 48 := by
  unfold a06892
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06891.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06884.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06866.pow 1)))

@[irreducible]
def a06893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06892 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06878 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a06885 ^ 1)
theorem ha06893 : a06893.IsHomogeneous 48 := by
  unfold a06893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06892.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06878.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha06885.pow 1)))

@[irreducible]
def a06894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06879 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06886 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a06893 ^ 1)
theorem ha06894 : a06894.IsHomogeneous 48 := by
  unfold a06894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06886.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha06893.pow 1)))

@[irreducible]
def a06895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06894 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06890 ^ 1)
theorem ha06895 : a06895.IsHomogeneous 48 := by
  unfold a06895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06894.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06890.pow 1)))

@[irreducible]
def a06896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00722 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01723 ^ 1)
theorem ha06896 : a06896.IsHomogeneous 50 := by
  unfold a06896
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01723.pow 1)))

@[irreducible]
def a06897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00722 ^ 1)
theorem ha06897 : a06897.IsHomogeneous 50 := by
  unfold a06897
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00722.pow 1)))

@[irreducible]
def a06898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06896 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06897 ^ 1)
theorem ha06898 : a06898.IsHomogeneous 50 := by
  unfold a06898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06896.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06897.pow 1)))

@[irreducible]
def a06899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00104 ^ 1)
theorem ha06899 : a06899.IsHomogeneous 25 := by
  unfold a06899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00104.pow 1)))

@[irreducible]
def a06900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a06899 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06897 ^ 1)
theorem ha06900 : a06900.IsHomogeneous 50 := by
  unfold a06900
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha06899.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06897.pow 1)))

@[irreducible]
def a06901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06898 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06900 ^ 1)
theorem ha06901 : a06901.IsHomogeneous 50 := by
  unfold a06901
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06900.pow 1)))

@[irreducible]
def a06902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01723 ^ 1)
theorem ha06902 : a06902.IsHomogeneous 49 := by
  unfold a06902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01723.pow 1)))

@[irreducible]
def a06903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06896 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06902 ^ 1)
theorem ha06903 : a06903.IsHomogeneous 50 := by
  unfold a06903
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06902.pow 1)))

@[irreducible]
def a06904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06898 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06903 ^ 1)
theorem ha06904 : a06904.IsHomogeneous 50 := by
  unfold a06904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06903.pow 1)))

@[irreducible]
def a06905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06904 ^ 1)
theorem ha06905 : a06905.IsHomogeneous 50 := by
  unfold a06905
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06904.pow 1)))

@[irreducible]
def a06906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a06785 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03600 ^ 1)
theorem ha06906 : a06906.IsHomogeneous 50 := by
  unfold a06906
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha06785.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03600.pow 1)))

@[irreducible]
def a06907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06906 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a06902 ^ 1)
theorem ha06907 : a06907.IsHomogeneous 50 := by
  unfold a06907
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06906.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha06902.pow 1)))

@[irreducible]
def a06908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06903 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a06907 ^ 1)
theorem ha06908 : a06908.IsHomogeneous 50 := by
  unfold a06908
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha06907.pow 1)))

@[irreducible]
def a06909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06908 ^ 1)
theorem ha06909 : a06909.IsHomogeneous 50 := by
  unfold a06909
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06908.pow 1)))

@[irreducible]
def a06910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06909 ^ 1)
theorem ha06910 : a06910.IsHomogeneous 50 := by
  unfold a06910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06909.pow 1)))

@[irreducible]
def a06911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1 * a01721 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a01469 ^ 1)
theorem ha06911 : a06911.IsHomogeneous 31 := by
  unfold a06911
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)).mul (ha01721.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha01469.pow 1)))

end CycleQ2Concrete
