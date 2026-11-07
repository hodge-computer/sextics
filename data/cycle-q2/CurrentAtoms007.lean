import Proposal.CurrentAtoms006

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a03584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a03583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03582 ^ 1)
theorem ha03584 : a03584.IsHomogeneous 189 := by
  unfold a03584
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha03583.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03582.pow 1)))

@[irreducible]
def a03585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a01724 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00723 ^ 1 * a00785 ^ 1)
theorem ha03585 : a03585.IsHomogeneous 164 := by
  unfold a03585
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha01724.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00723.pow 1)).mul (ha00785.pow 1)))

@[irreducible]
def a03586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a01852 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00723 ^ 1 * a00785 ^ 1)
theorem ha03586 : a03586.IsHomogeneous 164 := by
  unfold a03586
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha01852.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00723.pow 1)).mul (ha00785.pow 1)))

@[irreducible]
def a03587 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03585 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03586 ^ 1)
theorem ha03587 : a03587.IsHomogeneous 164 := by
  unfold a03587
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03585.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03586.pow 1)))

@[irreducible]
def a03588 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00717 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a01716 ^ 1)
theorem ha03588 : a03588.IsHomogeneous 45 := by
  unfold a03588
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01791 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03588 ^ 1)
theorem ha03589 : a03589.IsHomogeneous 45 := by
  unfold a03589
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01791.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03588.pow 1)))

@[irreducible]
def a03590 : Poly := (C ((-7 : ℂ) / (29160 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 3) + (C ((-1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1 * a02007 ^ 1)
theorem ha03590 : a03590.IsHomogeneous 36 := by
  unfold a03590
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (29160 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha02935.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a03591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a03590 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01716 ^ 1)
theorem ha03591 : a03591.IsHomogeneous 45 := by
  unfold a03591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha03590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03588 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03591 ^ 1)
theorem ha03592 : a03592.IsHomogeneous 45 := by
  unfold a03592
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03588.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03591.pow 1)))

@[irreducible]
def a03593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03589 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03592 ^ 1)
theorem ha03593 : a03593.IsHomogeneous 45 := by
  unfold a03593
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03589.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03592.pow 1)))

@[irreducible]
def a03594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01792 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03589 ^ 1)
theorem ha03594 : a03594.IsHomogeneous 45 := by
  unfold a03594
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03589.pow 1)))

@[irreducible]
def a03595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03593 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a03594 ^ 1)
theorem ha03595 : a03595.IsHomogeneous 45 := by
  unfold a03595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03593.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha03594.pow 1)))

@[irreducible]
def a03596 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00264 ^ 1 * a01721 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00721 ^ 2)
theorem ha03596 : a03596.IsHomogeneous 48 := by
  unfold a03596
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00264.pow 1)).mul (ha01721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00721.pow 2)))

@[irreducible]
def a03597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a02949 ^ 1) + (C ((7 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1)
theorem ha03597 : a03597.IsHomogeneous 19 := by
  unfold a03597
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha02949.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a03598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a03597 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a01721 ^ 1)
theorem ha03598 : a03598.IsHomogeneous 44 := by
  unfold a03598
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a03599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03598 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03596 ^ 1)
theorem ha03599 : a03599.IsHomogeneous 48 := by
  unfold a03599
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03598.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03596.pow 1)))

@[irreducible]
def a03600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03596 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03599 ^ 1)
theorem ha03600 : a03600.IsHomogeneous 48 := by
  unfold a03600
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03599.pow 1)))

@[irreducible]
def a03601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a03600 ^ 1) + (C ((21 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a03595 ^ 1)
theorem ha03601 : a03601.IsHomogeneous 52 := by
  unfold a03601
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha03600.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha03595.pow 1)))

@[irreducible]
def a03602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a01724 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a03601 ^ 1)
theorem ha03602 : a03602.IsHomogeneous 108 := by
  unfold a03602
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha01724.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha03601.pow 1)))

@[irreducible]
def a03603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a03602 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03585 ^ 1)
theorem ha03603 : a03603.IsHomogeneous 164 := by
  unfold a03603
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha03602.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03585.pow 1)))

@[irreducible]
def a03604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03603 ^ 1)
theorem ha03604 : a03604.IsHomogeneous 164 := by
  unfold a03604
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03603.pow 1)))

@[irreducible]
def a03605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00117 ^ 1 * a03604 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00270 ^ 1 * a01726 ^ 1)
theorem ha03605 : a03605.IsHomogeneous 189 := by
  unfold a03605
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00117.pow 1)).mul (ha03604.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00270.pow 1)).mul (ha01726.pow 1)))

@[irreducible]
def a03606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03582 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a03605 ^ 1)
theorem ha03606 : a03606.IsHomogeneous 189 := by
  unfold a03606
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha03605.pow 1)))

@[irreducible]
def a03607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03584 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03606 ^ 1)
theorem ha03607 : a03607.IsHomogeneous 189 := by
  unfold a03607
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03584.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03606.pow 1)))

@[irreducible]
def a03608 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00108 ^ 1)
theorem ha03608 : a03608.IsHomogeneous 18 := by
  unfold a03608
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00108.pow 1)))

@[irreducible]
def a03609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a01736 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a03608 ^ 1)
theorem ha03609 : a03609.IsHomogeneous 77 := by
  unfold a03609
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha01736.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha03608.pow 1)))

@[irreducible]
def a03610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03583 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00105 ^ 1 * a03609 ^ 1)
theorem ha03610 : a03610.IsHomogeneous 132 := by
  unfold a03610
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03583.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00105.pow 1)).mul (ha03609.pow 1)))

@[irreducible]
def a03611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a03610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03584 ^ 1)
theorem ha03611 : a03611.IsHomogeneous 189 := by
  unfold a03611
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha03610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03584.pow 1)))

@[irreducible]
def a03612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03611 ^ 1)
theorem ha03612 : a03612.IsHomogeneous 189 := by
  unfold a03612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03611.pow 1)))

@[irreducible]
def a03613 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a01739 ^ 1)
theorem ha03613 : a03613.IsHomogeneous 334 := by
  unfold a03613
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03612.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha01739.pow 1)))

@[irreducible]
def a03614 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03579 ^ 1)
theorem ha03614 : a03614.IsHomogeneous 479 := by
  unfold a03614
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03579.pow 1)))

@[irreducible]
def a03615 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03581 ^ 1)
theorem ha03615 : a03615.IsHomogeneous 624 := by
  unfold a03615
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03581.pow 1)))

@[irreducible]
def a03616 : Poly := (C ((-5 : ℂ) / (2916 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a01742 ^ 1)
theorem ha03616 : a03616.IsHomogeneous 476 := by
  unfold a03616
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2916 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha01742.pow 1)))

@[irreducible]
def a03617 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 2)
theorem ha03617 : a03617.IsHomogeneous 290 := by
  unfold a03617
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 2)))

@[irreducible]
def a03618 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03617 ^ 1)
theorem ha03618 : a03618.IsHomogeneous 290 := by
  unfold a03618
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03617.pow 1)))

@[irreducible]
def a03619 : Poly := (C ((-5 : ℂ) / (2916 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a00775 ^ 1)
theorem ha03619 : a03619.IsHomogeneous 331 := by
  unfold a03619
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2916 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha00775.pow 1)))

@[irreducible]
def a03620 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a03619 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a03618 ^ 1)
theorem ha03620 : a03620.IsHomogeneous 435 := by
  unfold a03620
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha03619.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha03618.pow 1)))

@[irreducible]
def a03621 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a01742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a03620 ^ 1)
theorem ha03621 : a03621.IsHomogeneous 580 := by
  unfold a03621
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha01742.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha03620.pow 1)))

@[irreducible]
def a03622 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a03616 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03621 ^ 1)
theorem ha03622 : a03622.IsHomogeneous 580 := by
  unfold a03622
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha03616.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03621.pow 1)))

@[irreducible]
def a03623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a00262 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00123 ^ 1 * a00737 ^ 1)
theorem ha03623 : a03623.IsHomogeneous 179 := by
  unfold a03623
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a03624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00773 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00285 ^ 1)
theorem ha03624 : a03624.IsHomogeneous 139 := by
  unfold a03624
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00285.pow 1)))

@[irreducible]
def a03625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00123 ^ 1 * a00262 ^ 1)
theorem ha03625 : a03625.IsHomogeneous 139 := by
  unfold a03625
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00123.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a03624 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a03625 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03623 ^ 1)
theorem ha03626 : a03626.IsHomogeneous 181 := by
  unfold a03626
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha03624.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha03625.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03623.pow 1)))

@[irreducible]
def a03627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a00737 ^ 1)
theorem ha03627 : a03627.IsHomogeneous 179 := by
  unfold a03627
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a03628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00737 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01750 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a00737 ^ 1)
theorem ha03628 : a03628.IsHomogeneous 179 := by
  unfold a03628
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01750.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a03629 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03623 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03627 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03628 ^ 1)
theorem ha03629 : a03629.IsHomogeneous 179 := by
  unfold a03629
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03627.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03628.pow 1)))

@[irreducible]
def a03630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00773 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00773 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a01822 ^ 1)
theorem ha03630 : a03630.IsHomogeneous 138 := by
  unfold a03630
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a03631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a03624 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a03630 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03627 ^ 1)
theorem ha03631 : a03631.IsHomogeneous 181 := by
  unfold a03631
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha03624.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha03630.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03627.pow 1)))

@[irreducible]
def a03632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03626 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03631 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03629 ^ 1)
theorem ha03632 : a03632.IsHomogeneous 181 := by
  unfold a03632
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03626.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03631.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03629.pow 1)))

@[irreducible]
def a03633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00285 ^ 1 * a00737 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a01750 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a00773 ^ 1)
theorem ha03633 : a03633.IsHomogeneous 184 := by
  unfold a03633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00285.pow 1)).mul (ha00737.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha00773.pow 1)))

@[irreducible]
def a03634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a00773 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1)
theorem ha03634 : a03634.IsHomogeneous 184 := by
  unfold a03634
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha00773.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)))

@[irreducible]
def a03635 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03627 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a03633 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a03634 ^ 1)
theorem ha03635 : a03635.IsHomogeneous 184 := by
  unfold a03635
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha03633.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha03634.pow 1)))

@[irreducible]
def a03636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a01716 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00717 ^ 2)
theorem ha03636 : a03636.IsHomogeneous 80 := by
  unfold a03636
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha01716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00717.pow 2)))

@[irreducible]
def a03637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a03590 ^ 1)
theorem ha03637 : a03637.IsHomogeneous 79 := by
  unfold a03637
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a03638 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03636 ^ 1)
theorem ha03638 : a03638.IsHomogeneous 80 := by
  unfold a03638
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03637.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03636.pow 1)))

@[irreducible]
def a03639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03636 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03638 ^ 1)
theorem ha03639 : a03639.IsHomogeneous 80 := by
  unfold a03639
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03636.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03638.pow 1)))

@[irreducible]
def a03640 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a03639 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00123 ^ 1 * a01750 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a01750 ^ 1)
theorem ha03640 : a03640.IsHomogeneous 184 := by
  unfold a03640
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha03639.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00123.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a03641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03628 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a03640 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a03633 ^ 1)
theorem ha03641 : a03641.IsHomogeneous 184 := by
  unfold a03641
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha03640.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha03633.pow 1)))

@[irreducible]
def a03642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03629 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03635 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03641 ^ 1)
theorem ha03642 : a03642.IsHomogeneous 184 := by
  unfold a03642
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03635.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03641.pow 1)))

@[irreducible]
def a03643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00276 ^ 1 * a01776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00749 ^ 1 * a00751 ^ 1)
theorem ha03643 : a03643.IsHomogeneous 89 := by
  unfold a03643
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00276.pow 1)).mul (ha01776.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00749.pow 1)).mul (ha00751.pow 1)))

@[irreducible]
def a03644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00275 ^ 1 * a01779 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00749 ^ 1 * a00751 ^ 1)
theorem ha03644 : a03644.IsHomogeneous 89 := by
  unfold a03644
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00275.pow 1)).mul (ha01779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00749.pow 1)).mul (ha00751.pow 1)))

@[irreducible]
def a03645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03643 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a03644 ^ 1)
theorem ha03645 : a03645.IsHomogeneous 89 := by
  unfold a03645
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03643.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha03644.pow 1)))

@[irreducible]
def a03646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00717 ^ 1)
theorem ha03646 : a03646.IsHomogeneous 46 := by
  unfold a03646
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a03647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1)
theorem ha03647 : a03647.IsHomogeneous 48 := by
  unfold a03647
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1)
theorem ha03648 : a03648.IsHomogeneous 48 := by
  unfold a03648
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03647 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03648 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03646 ^ 1)
theorem ha03649 : a03649.IsHomogeneous 48 := by
  unfold a03649
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03647.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03648.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03646.pow 1)))

@[irreducible]
def a03650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00262 ^ 1)
theorem ha03650 : a03650.IsHomogeneous 46 := by
  unfold a03650
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)))

@[irreducible]
def a03651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00717 ^ 1)
theorem ha03651 : a03651.IsHomogeneous 46 := by
  unfold a03651
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a03652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03646 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03650 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03651 ^ 1)
theorem ha03652 : a03652.IsHomogeneous 46 := by
  unfold a03652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03650.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03651.pow 1)))

@[irreducible]
def a03653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha03653 : a03653.IsHomogeneous 42 := by
  unfold a03653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a03654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03647 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03653 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03650 ^ 1)
theorem ha03654 : a03654.IsHomogeneous 48 := by
  unfold a03654
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03647.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03653.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03650.pow 1)))

@[irreducible]
def a03655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03654 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03652 ^ 1)
theorem ha03655 : a03655.IsHomogeneous 48 := by
  unfold a03655
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03654.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03652.pow 1)))

@[irreducible]
def a03656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00009 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a01716 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 5 * a00130 ^ 1 * a00717 ^ 1)
theorem ha03656 : a03656.IsHomogeneous 51 := by
  unfold a03656
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00009.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 5)).mul (ha00130.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a03657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00262 ^ 1)
theorem ha03657 : a03657.IsHomogeneous 46 := by
  unfold a03657
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)))

@[irreducible]
def a03658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03650 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a03657 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a03656 ^ 1)
theorem ha03658 : a03658.IsHomogeneous 51 := by
  unfold a03658
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03650.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha03657.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha03656.pow 1)))

@[irreducible]
def a03659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00025 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01716 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a01716 ^ 1)
theorem ha03659 : a03659.IsHomogeneous 51 := by
  unfold a03659
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha03590.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03651 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03659 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a03656 ^ 1)
theorem ha03660 : a03660.IsHomogeneous 51 := by
  unfold a03660
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03659.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha03656.pow 1)))

@[irreducible]
def a03661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03652 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03658 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03660 ^ 1)
theorem ha03661 : a03661.IsHomogeneous 51 := by
  unfold a03661
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03652.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03658.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03660.pow 1)))

@[irreducible]
def a03662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00009 ^ 1 * a00262 ^ 1)
theorem ha03662 : a03662.IsHomogeneous 48 := by
  unfold a03662
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03662 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03653 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03657 ^ 1)
theorem ha03663 : a03663.IsHomogeneous 48 := by
  unfold a03663
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03662.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03653.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03657.pow 1)))

@[irreducible]
def a03664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03654 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a03663 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03658 ^ 1)
theorem ha03664 : a03664.IsHomogeneous 51 := by
  unfold a03664
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03654.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha03663.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03658.pow 1)))

@[irreducible]
def a03665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03664 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03661 ^ 1)
theorem ha03665 : a03665.IsHomogeneous 51 := by
  unfold a03665
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03655.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03664.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03661.pow 1)))

@[irreducible]
def a03666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00722 ^ 1)
theorem ha03666 : a03666.IsHomogeneous 50 := by
  unfold a03666
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00722.pow 1)))

@[irreducible]
def a03667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00104 ^ 1)
theorem ha03667 : a03667.IsHomogeneous 25 := by
  unfold a03667
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00104.pow 1)))

@[irreducible]
def a03668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a03667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03666 ^ 1)
theorem ha03668 : a03668.IsHomogeneous 50 := by
  unfold a03668
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha03667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03666.pow 1)))

@[irreducible]
def a03669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00722 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a01723 ^ 1)
theorem ha03669 : a03669.IsHomogeneous 50 := by
  unfold a03669
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha01723.pow 1)))

@[irreducible]
def a03670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03666 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03669 ^ 1)
theorem ha03670 : a03670.IsHomogeneous 50 := by
  unfold a03670
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03669.pow 1)))

@[irreducible]
def a03671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03670 ^ 1)
theorem ha03671 : a03671.IsHomogeneous 50 := by
  unfold a03671
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03670.pow 1)))

@[irreducible]
def a03672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01723 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00009 ^ 1 * a03600 ^ 1)
theorem ha03672 : a03672.IsHomogeneous 54 := by
  unfold a03672
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01723.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)).mul (ha03600.pow 1)))

@[irreducible]
def a03673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03669 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a03672 ^ 1)
theorem ha03673 : a03673.IsHomogeneous 54 := by
  unfold a03673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha03672.pow 1)))

@[irreducible]
def a03674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03670 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03673 ^ 1)
theorem ha03674 : a03674.IsHomogeneous 54 := by
  unfold a03674
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03670.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03673.pow 1)))

@[irreducible]
def a03675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03671 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03674 ^ 1)
theorem ha03675 : a03675.IsHomogeneous 54 := by
  unfold a03675
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03671.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03674.pow 1)))

@[irreducible]
def a03676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00025 ^ 1 * a00130 ^ 1 * a01721 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00574 ^ 1 * a00721 ^ 1)
theorem ha03676 : a03676.IsHomogeneous 36 := by
  unfold a03676
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00574.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a03677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00264 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00574 ^ 1 * a00721 ^ 1)
theorem ha03677 : a03677.IsHomogeneous 36 := by
  unfold a03677
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00264.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00574.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a03678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03676 ^ 1) + (C ((168 : ℂ) / (5 : ℂ)) * a03677 ^ 1)
theorem ha03678 : a03678.IsHomogeneous 36 := by
  unfold a03678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((168 : ℂ) / (5 : ℂ))).mul (ha03677.pow 1)))

@[irreducible]
def a03679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01721 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00025 ^ 1 * a03597 ^ 1)
theorem ha03679 : a03679.IsHomogeneous 25 := by
  unfold a03679
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00025.pow 1)).mul (ha03597.pow 1)))

@[irreducible]
def a03680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00025 ^ 1 * a03679 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03676 ^ 1)
theorem ha03680 : a03680.IsHomogeneous 36 := by
  unfold a03680
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00025.pow 1)).mul (ha03679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03676.pow 1)))

@[irreducible]
def a03681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03680 ^ 1)
theorem ha03681 : a03681.IsHomogeneous 36 := by
  unfold a03681
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03680.pow 1)))

@[irreducible]
def a03682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a03186 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00264 ^ 1 * a01469 ^ 1)
theorem ha03682 : a03682.IsHomogeneous 31 := by
  unfold a03682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00264.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a03683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a03682 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03677 ^ 1)
theorem ha03683 : a03683.IsHomogeneous 36 := by
  unfold a03683
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha03682.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03677.pow 1)))

@[irreducible]
def a03684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03678 ^ 1) + (C ((14 : ℂ) / (1 : ℂ)) * a03683 ^ 1)
theorem ha03684 : a03684.IsHomogeneous 36 := by
  unfold a03684
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (1 : ℂ))).mul (ha03683.pow 1)))

@[irreducible]
def a03685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03681 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03684 ^ 1)
theorem ha03685 : a03685.IsHomogeneous 36 := by
  unfold a03685
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03681.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03684.pow 1)))

@[irreducible]
def a03686 : Poly := (C ((-1 : ℂ) / (576 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a03685 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a03675 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a03665 ^ 1)
theorem ha03686 : a03686.IsHomogeneous 58 := by
  unfold a03686
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (576 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha03685.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha03675.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha03665.pow 1)))

@[irreducible]
def a03687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00276 ^ 1 * a01776 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00120 ^ 1 * a03686 ^ 1)
theorem ha03687 : a03687.IsHomogeneous 89 := by
  unfold a03687
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00276.pow 1)).mul (ha01776.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00120.pow 1)).mul (ha03686.pow 1)))

@[irreducible]
def a03688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03643 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03687 ^ 1)
theorem ha03688 : a03688.IsHomogeneous 89 := by
  unfold a03688
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03643.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03687.pow 1)))

@[irreducible]
def a03689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03645 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03688 ^ 1)
theorem ha03689 : a03689.IsHomogeneous 89 := by
  unfold a03689
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03688.pow 1)))

@[irreducible]
def a03690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00119 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 2 * a02935 ^ 1) + (C ((7 : ℂ) / (135 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1)
theorem ha03690 : a03690.IsHomogeneous 25 := by
  unfold a03690
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00119.pow 1)).mul (ha02007.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 2)).mul (ha02935.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (135 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a03691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00118 ^ 1 * a03690 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00275 ^ 1 * a01779 ^ 1)
theorem ha03691 : a03691.IsHomogeneous 89 := by
  unfold a03691
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00118.pow 1)).mul (ha03690.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00275.pow 1)).mul (ha01779.pow 1)))

@[irreducible]
def a03692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03644 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a03691 ^ 1)
theorem ha03692 : a03692.IsHomogeneous 89 := by
  unfold a03692
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha03691.pow 1)))

@[irreducible]
def a03693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03645 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a03692 ^ 1)
theorem ha03693 : a03693.IsHomogeneous 89 := by
  unfold a03693
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03645.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha03692.pow 1)))

@[irreducible]
def a03694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03693 ^ 1)
theorem ha03694 : a03694.IsHomogeneous 89 := by
  unfold a03694
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03693.pow 1)))

@[irreducible]
def a03695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a00762 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00280 ^ 1 * a00717 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00262 ^ 1 * a00280 ^ 1)
theorem ha03695 : a03695.IsHomogeneous 92 := by
  unfold a03695
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a03696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00717 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha03696 : a03696.IsHomogeneous 88 := by
  unfold a03696
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a03697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a00280 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a01716 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 5 * a00121 ^ 1 * a00717 ^ 1)
theorem ha03697 : a03697.IsHomogeneous 93 := by
  unfold a03697
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 5)).mul (ha00121.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a03698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03695 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03697 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a03696 ^ 1)
theorem ha03698 : a03698.IsHomogeneous 93 := by
  unfold a03698
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03697.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha03696.pow 1)))

@[irreducible]
def a03699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00280 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00762 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha03699 : a03699.IsHomogeneous 88 := by
  unfold a03699
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a03700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a00262 ^ 1 * a00762 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a01801 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00762 ^ 1)
theorem ha03700 : a03700.IsHomogeneous 93 := by
  unfold a03700
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha01801.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a03701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03695 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03700 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a03699 ^ 1)
theorem ha03701 : a03701.IsHomogeneous 93 := by
  unfold a03701
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03700.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha03699.pow 1)))

@[irreducible]
def a03702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00121 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00103 ^ 1 * a00280 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00121 ^ 1 * a00262 ^ 1)
theorem ha03702 : a03702.IsHomogeneous 90 := by
  unfold a03702
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00121.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00103.pow 1)).mul (ha00280.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00121.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03702 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03696 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03699 ^ 1)
theorem ha03703 : a03703.IsHomogeneous 90 := by
  unfold a03703
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03696.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03699.pow 1)))

@[irreducible]
def a03704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03703 ^ 1) + (C ((27 : ℂ) / (7 : ℂ)) * a03698 ^ 1) + (C ((27 : ℂ) / (7 : ℂ)) * a03701 ^ 1)
theorem ha03704 : a03704.IsHomogeneous 93 := by
  unfold a03704
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (7 : ℂ))).mul (ha03698.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (7 : ℂ))).mul (ha03701.pow 1)))

@[irreducible]
def a03705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1 * a00762 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00280 ^ 1 * a01716 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00280 ^ 1 * a00717 ^ 1)
theorem ha03705 : a03705.IsHomogeneous 92 := by
  unfold a03705
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha00762.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a03706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1 * a00762 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00262 ^ 1 * a01801 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a00762 ^ 1)
theorem ha03706 : a03706.IsHomogeneous 92 := by
  unfold a03706
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha00762.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a03707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03695 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03705 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03706 ^ 1)
theorem ha03707 : a03707.IsHomogeneous 92 := by
  unfold a03707
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03695.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03705.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03706.pow 1)))

@[irreducible]
def a03708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00280 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00121 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a01716 ^ 1)
theorem ha03708 : a03708.IsHomogeneous 93 := by
  unfold a03708
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03705 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03708 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a03697 ^ 1)
theorem ha03709 : a03709.IsHomogeneous 93 := by
  unfold a03709
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03705.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03708.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha03697.pow 1)))

@[irreducible]
def a03710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03698 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03709 ^ 1)
theorem ha03710 : a03710.IsHomogeneous 93 := by
  unfold a03710
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03698.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03709.pow 1)))

@[irreducible]
def a03711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00717 ^ 1)
theorem ha03711 : a03711.IsHomogeneous 40 := by
  unfold a03711
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a03712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha03712 : a03712.IsHomogeneous 42 := by
  unfold a03712
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a03713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03712 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03711 ^ 1)
theorem ha03713 : a03713.IsHomogeneous 42 := by
  unfold a03713
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03711.pow 1)))

@[irreducible]
def a03714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a01716 ^ 1)
theorem ha03714 : a03714.IsHomogeneous 40 := by
  unfold a03714
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03711 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03714 ^ 1)
theorem ha03715 : a03715.IsHomogeneous 40 := by
  unfold a03715
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03711.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03714.pow 1)))

@[irreducible]
def a03716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03713 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03715 ^ 1)
theorem ha03716 : a03716.IsHomogeneous 42 := by
  unfold a03716
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03713.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03715.pow 1)))

@[irreducible]
def a03717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01716 ^ 1)
theorem ha03717 : a03717.IsHomogeneous 42 := by
  unfold a03717
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha03590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01716.pow 1)))

@[irreducible]
def a03718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03717 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a03714 ^ 1)
theorem ha03718 : a03718.IsHomogeneous 42 := by
  unfold a03718
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha03714.pow 1)))

@[irreducible]
def a03719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03718 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03715 ^ 1)
theorem ha03719 : a03719.IsHomogeneous 42 := by
  unfold a03719
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03718.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03715.pow 1)))

@[irreducible]
def a03720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03719 ^ 1)
theorem ha03720 : a03720.IsHomogeneous 42 := by
  unfold a03720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03719.pow 1)))

@[irreducible]
def a03721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01721 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha03721 : a03721.IsHomogeneous 25 := by
  unfold a03721
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a03722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01811 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03721 ^ 1)
theorem ha03722 : a03722.IsHomogeneous 25 := by
  unfold a03722
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01811.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03721.pow 1)))

@[irreducible]
def a03723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01812 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03722 ^ 1)
theorem ha03723 : a03723.IsHomogeneous 25 := by
  unfold a03723
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01812.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03722.pow 1)))

@[irreducible]
def a03724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a03597 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01721 ^ 1)
theorem ha03724 : a03724.IsHomogeneous 25 := by
  unfold a03724
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a03725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03721 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03724 ^ 1)
theorem ha03725 : a03725.IsHomogeneous 25 := by
  unfold a03725
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03724.pow 1)))

@[irreducible]
def a03726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03722 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03725 ^ 1)
theorem ha03726 : a03726.IsHomogeneous 25 := by
  unfold a03726
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03725.pow 1)))

@[irreducible]
def a03727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03723 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03726 ^ 1)
theorem ha03727 : a03727.IsHomogeneous 25 := by
  unfold a03727
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03726.pow 1)))

@[irreducible]
def a03728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03720 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a03727 ^ 1)
theorem ha03728 : a03728.IsHomogeneous 42 := by
  unfold a03728
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03720.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha03727.pow 1)))

@[irreducible]
def a03729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a01801 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00103 ^ 1 * a03728 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a01801 ^ 1)
theorem ha03729 : a03729.IsHomogeneous 93 := by
  unfold a03729
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha03728.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a03730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03706 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a03729 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03700 ^ 1)
theorem ha03730 : a03730.IsHomogeneous 93 := by
  unfold a03730
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03706.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha03729.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03700.pow 1)))

@[irreducible]
def a03731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03701 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03730 ^ 1)
theorem ha03731 : a03731.IsHomogeneous 93 := by
  unfold a03731
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03701.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03730.pow 1)))

@[irreducible]
def a03732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03704 ^ 1) + (C ((27 : ℂ) / (7 : ℂ)) * a03710 ^ 1) + (C ((27 : ℂ) / (7 : ℂ)) * a03731 ^ 1)
theorem ha03732 : a03732.IsHomogeneous 93 := by
  unfold a03732
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03704.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (7 : ℂ))).mul (ha03710.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (7 : ℂ))).mul (ha03731.pow 1)))

@[irreducible]
def a03733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00133 ^ 1 * a00262 ^ 1 * a00769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a00717 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00262 ^ 1 * a00283 ^ 1 * a00324 ^ 1)
theorem ha03733 : a03733.IsHomogeneous 77 := by
  unfold a03733
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00262.pow 1)).mul (ha00283.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00283 ^ 1 * a01716 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00717 ^ 1 * a00769 ^ 1)
theorem ha03734 : a03734.IsHomogeneous 77 := by
  unfold a03734
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha00717.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha01716.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a03735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00717 ^ 1 * a00769 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a00769 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 5 * a00032 ^ 1 * a00262 ^ 1 * a01816 ^ 1)
theorem ha03735 : a03735.IsHomogeneous 76 := by
  unfold a03735
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 5)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a03736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03733 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03734 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a03735 ^ 1)
theorem ha03736 : a03736.IsHomogeneous 77 := by
  unfold a03736
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03733.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03734.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha03735.pow 1)))

@[irreducible]
def a03737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00324 ^ 1 * a00717 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00003 ^ 1 * a00122 ^ 1 * a00133 ^ 1 * a01716 ^ 1)
theorem ha03737 : a03737.IsHomogeneous 77 := by
  unfold a03737
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha00717.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00003.pow 1)).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00324 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00262 ^ 1 * a00283 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00122 ^ 1 * a00262 ^ 1)
theorem ha03738 : a03738.IsHomogeneous 77 := by
  unfold a03738
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00262.pow 1)).mul (ha00283.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00122.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03733 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03737 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03738 ^ 1)
theorem ha03739 : a03739.IsHomogeneous 77 := by
  unfold a03739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03733.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03737.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03738.pow 1)))

@[irreducible]
def a03740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00122 ^ 1 * a03590 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a01716 ^ 1)
theorem ha03740 : a03740.IsHomogeneous 76 := by
  unfold a03740
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a03741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03734 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03740 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03737 ^ 1)
theorem ha03741 : a03741.IsHomogeneous 77 := by
  unfold a03741
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03734.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03740.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03737.pow 1)))

@[irreducible]
def a03742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03741 ^ 1)
theorem ha03742 : a03742.IsHomogeneous 77 := by
  unfold a03742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03739.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03741.pow 1)))

@[irreducible]
def a03743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00133 ^ 1 * a00262 ^ 1 * a00769 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00133 ^ 1 * a01816 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00324 ^ 1 * a00769 ^ 1)
theorem ha03743 : a03743.IsHomogeneous 78 := by
  unfold a03743
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a03744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a00283 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a00283 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a00324 ^ 1 * a00769 ^ 1)
theorem ha03744 : a03744.IsHomogeneous 78 := by
  unfold a03744
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha00283.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a03745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03733 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03743 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a03744 ^ 1)
theorem ha03745 : a03745.IsHomogeneous 78 := by
  unfold a03745
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03733.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03743.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha03744.pow 1)))

@[irreducible]
def a03746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha03746 : a03746.IsHomogeneous 25 := by
  unfold a03746
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a03747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00264 ^ 1)
theorem ha03747 : a03747.IsHomogeneous 25 := by
  unfold a03747
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)))

@[irreducible]
def a03748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03746 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03747 ^ 1)
theorem ha03748 : a03748.IsHomogeneous 25 := by
  unfold a03748
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03747.pow 1)))

@[irreducible]
def a03749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00721 ^ 1)
theorem ha03749 : a03749.IsHomogeneous 24 := by
  unfold a03749
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00721.pow 1)))

@[irreducible]
def a03750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03746 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a03749 ^ 1)
theorem ha03750 : a03750.IsHomogeneous 25 := by
  unfold a03750
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03746.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha03749.pow 1)))

@[irreducible]
def a03751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03748 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03750 ^ 1)
theorem ha03751 : a03751.IsHomogeneous 25 := by
  unfold a03751
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03750.pow 1)))

@[irreducible]
def a03752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a03597 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01721 ^ 1)
theorem ha03752 : a03752.IsHomogeneous 25 := by
  unfold a03752
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01721.pow 1)))

@[irreducible]
def a03753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03752 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a03749 ^ 1)
theorem ha03753 : a03753.IsHomogeneous 25 := by
  unfold a03753
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03752.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha03749.pow 1)))

@[irreducible]
def a03754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03750 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03753 ^ 1)
theorem ha03754 : a03754.IsHomogeneous 25 := by
  unfold a03754
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03750.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03753.pow 1)))

@[irreducible]
def a03755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03751 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03754 ^ 1)
theorem ha03755 : a03755.IsHomogeneous 25 := by
  unfold a03755
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03751.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03754.pow 1)))

@[irreducible]
def a03756 : Poly := (C ((-7 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a03186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03755 ^ 1)
theorem ha03756 : a03756.IsHomogeneous 25 := by
  unfold a03756
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha03186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03755.pow 1)))

@[irreducible]
def a03757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00103 ^ 1 * a03756 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a01816 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00262 ^ 1 * a01816 ^ 1)
theorem ha03757 : a03757.IsHomogeneous 73 := by
  unfold a03757
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha03756.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha01816.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a03758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a03735 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03743 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00003 ^ 5 * a03757 ^ 1)
theorem ha03758 : a03758.IsHomogeneous 78 := by
  unfold a03758
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha03735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03743.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00003.pow 5)).mul (ha03757.pow 1)))

@[irreducible]
def a03759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03745 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a03758 ^ 1)
theorem ha03759 : a03759.IsHomogeneous 78 := by
  unfold a03759
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03745.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha03758.pow 1)))

@[irreducible]
def a03760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00103 ^ 1 * a00283 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00122 ^ 1 * a00262 ^ 1)
theorem ha03760 : a03760.IsHomogeneous 73 := by
  unfold a03760
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00122.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a03761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03738 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 5 * a03760 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03744 ^ 1)
theorem ha03761 : a03761.IsHomogeneous 78 := by
  unfold a03761
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03738.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 5)).mul (ha03760.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03744.pow 1)))

@[irreducible]
def a03762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03745 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03761 ^ 1)
theorem ha03762 : a03762.IsHomogeneous 78 := by
  unfold a03762
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03745.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03761.pow 1)))

@[irreducible]
def a03763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03759 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03762 ^ 1)
theorem ha03763 : a03763.IsHomogeneous 78 := by
  unfold a03763
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03742.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03759.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03762.pow 1)))

@[irreducible]
def a03764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a03694 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a03763 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a03732 ^ 1)
theorem ha03764 : a03764.IsHomogeneous 94 := by
  unfold a03764
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha03694.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha03763.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha03732.pow 1)))

@[irreducible]
def a03765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00262 ^ 1 * a01822 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a03764 ^ 1)
theorem ha03765 : a03765.IsHomogeneous 142 := by
  unfold a03765
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha01822.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a03766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a03630 ^ 1) + (C ((864 : ℂ) / (25 : ℂ)) * a00103 ^ 1 * a03765 ^ 1) + (C ((864 : ℂ) / (25 : ℂ)) * a03634 ^ 1)
theorem ha03766 : a03766.IsHomogeneous 184 := by
  unfold a03766
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha03630.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((864 : ℂ) / (25 : ℂ))).mul (ha00103.pow 1)).mul (ha03765.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((864 : ℂ) / (25 : ℂ))).mul (ha03634.pow 1)))

@[irreducible]
def a03767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03631 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03766 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a03635 ^ 1)
theorem ha03767 : a03767.IsHomogeneous 184 := by
  unfold a03767
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03631.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03766.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha03635.pow 1)))

@[irreducible]
def a03768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03767 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03642 ^ 1)
theorem ha03768 : a03768.IsHomogeneous 184 := by
  unfold a03768
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03632.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03767.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03642.pow 1)))

@[irreducible]
def a03769 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a01825 ^ 1)
theorem ha03769 : a03769.IsHomogeneous 330 := by
  unfold a03769
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha01825.pow 1)))

@[irreducible]
def a03770 : Poly := (C ((-5 : ℂ) / (2916 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03616 ^ 1)
theorem ha03770 : a03770.IsHomogeneous 476 := by
  unfold a03770
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2916 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03616.pow 1)))

@[irreducible]
def a03771 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a03770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03622 ^ 1)
theorem ha03771 : a03771.IsHomogeneous 580 := by
  unfold a03771
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha03770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03622.pow 1)))

@[irreducible]
def a03772 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1 * a01827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a03771 ^ 1)
theorem ha03772 : a03772.IsHomogeneous 659 := by
  unfold a03772
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).mul (ha01827.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha03771.pow 1)))

@[irreducible]
def a03773 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03580 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a03772 ^ 1)
theorem ha03773 : a03773.IsHomogeneous 714 := by
  unfold a03773
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03580.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha03772.pow 1)))

@[irreducible]
def a03774 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a03773 ^ 1)
theorem ha03774 : a03774.IsHomogeneous 769 := by
  unfold a03774
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha03773.pow 1)))

@[irreducible]
def a03775 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03774 ^ 1)
theorem ha03775 : a03775.IsHomogeneous 769 := by
  unfold a03775
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03615.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03774.pow 1)))

@[irreducible]
def a03776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03775 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00291 ^ 1 * a01830 ^ 1)
theorem ha03776 : a03776.IsHomogeneous 884 := by
  unfold a03776
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03775.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00291.pow 1)).mul (ha01830.pow 1)))

@[irreducible]
def a03777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03776 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a03576 ^ 1)
theorem ha03777 : a03777.IsHomogeneous 944 := by
  unfold a03777
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03776.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha03576.pow 1)))

@[irreducible]
def a03778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03777 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a03578 ^ 1)
theorem ha03778 : a03778.IsHomogeneous 1004 := by
  unfold a03778
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03777.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha03578.pow 1)))

@[irreducible]
def a03779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a01833 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a01866 ^ 1)
theorem ha03779 : a03779.IsHomogeneous 812 := by
  unfold a03779
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha01833.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a03780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1)
theorem ha03780 : a03780.IsHomogeneous 594 := by
  unfold a03780
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha00792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a03781 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 2)
theorem ha03781 : a03781.IsHomogeneous 436 := by
  unfold a03781
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 2)))

@[irreducible]
def a03782 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03781 ^ 1)
theorem ha03782 : a03782.IsHomogeneous 436 := by
  unfold a03782
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03781.pow 1)))

@[irreducible]
def a03783 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a03780 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a03782 ^ 1)
theorem ha03783 : a03783.IsHomogeneous 654 := by
  unfold a03783
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha03780.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha03782.pow 1)))

@[irreducible]
def a03784 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a01833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a03783 ^ 1)
theorem ha03784 : a03784.IsHomogeneous 872 := by
  unfold a03784
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha01833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha03783.pow 1)))

@[irreducible]
def a03785 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a03779 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03784 ^ 1)
theorem ha03785 : a03785.IsHomogeneous 872 := by
  unfold a03785
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha03779.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03784.pow 1)))

@[irreducible]
def a03786 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a01855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00787 ^ 1 * a00790 ^ 1)
theorem ha03786 : a03786.IsHomogeneous 382 := by
  unfold a03786
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha01855.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00787.pow 1)).mul (ha00790.pow 1)))

@[irreducible]
def a03787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00787 ^ 1 * a00790 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00290 ^ 1 * a01863 ^ 1)
theorem ha03787 : a03787.IsHomogeneous 473 := by
  unfold a03787
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00787.pow 1)).mul (ha00790.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00290.pow 1)).mul (ha01863.pow 1)))

@[irreducible]
def a03788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03787 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03786 ^ 1)
theorem ha03788 : a03788.IsHomogeneous 479 := by
  unfold a03788
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03787.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03786.pow 1)))

@[irreducible]
def a03789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00783 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00289 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1)
theorem ha03789 : a03789.IsHomogeneous 174 := by
  unfold a03789
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1)))

@[irreducible]
def a03790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00289 ^ 1 * a01841 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a00783 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00289 ^ 1)
theorem ha03790 : a03790.IsHomogeneous 125 := by
  unfold a03790
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00783.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)))

@[irreducible]
def a03791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a00783 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a01848 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00783 ^ 1)
theorem ha03791 : a03791.IsHomogeneous 119 := by
  unfold a03791
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00783.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha01848.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a03792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a03790 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a03791 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03789 ^ 1)
theorem ha03792 : a03792.IsHomogeneous 180 := by
  unfold a03792
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha03790.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03791.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03789.pow 1)))

@[irreducible]
def a03793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00155 ^ 1 * a00785 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00289 ^ 1)
theorem ha03793 : a03793.IsHomogeneous 182 := by
  unfold a03793
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha00785.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)))

@[irreducible]
def a03794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00155 ^ 1 * a00785 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a01852 ^ 1)
theorem ha03794 : a03794.IsHomogeneous 176 := by
  unfold a03794
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha00785.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a03795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03793 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03794 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a03789 ^ 1)
theorem ha03795 : a03795.IsHomogeneous 182 := by
  unfold a03795
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03793.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03794.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha03789.pow 1)))

@[irreducible]
def a03796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01839 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha03796 : a03796.IsHomogeneous 6 := by
  unfold a03796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a03797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha03797 : a03797.IsHomogeneous 6 := by
  unfold a03797
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03797 ^ 1) + (C ((25 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03796 ^ 1)
theorem ha03798 : a03798.IsHomogeneous 12 := by
  unfold a03798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03797.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03796.pow 1)))

@[irreducible]
def a03799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00518 ^ 1)
theorem ha03799 : a03799.IsHomogeneous 6 := by
  unfold a03799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00518.pow 1)))

@[irreducible]
def a03800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03799 ^ 1)
theorem ha03800 : a03800.IsHomogeneous 12 := by
  unfold a03800
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03799.pow 1)))

@[irreducible]
def a03801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03800 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01839 ^ 1)
theorem ha03801 : a03801.IsHomogeneous 12 := by
  unfold a03801
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03800.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01839.pow 1)))

@[irreducible]
def a03802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03801 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03796 ^ 1)
theorem ha03802 : a03802.IsHomogeneous 12 := by
  unfold a03802
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03801.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03796.pow 1)))

@[irreducible]
def a03803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03798 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03802 ^ 1)
theorem ha03803 : a03803.IsHomogeneous 18 := by
  unfold a03803
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03798.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03802.pow 1)))

@[irreducible]
def a03804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00289 ^ 1 * a01841 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a01841 ^ 1)
theorem ha03804 : a03804.IsHomogeneous 133 := by
  unfold a03804
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03803.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha01841.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a03805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a03804 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a03790 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03793 ^ 1)
theorem ha03805 : a03805.IsHomogeneous 188 := by
  unfold a03805
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha03804.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03790.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03793.pow 1)))

@[irreducible]
def a03806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03805 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a03792 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03795 ^ 1)
theorem ha03806 : a03806.IsHomogeneous 188 := by
  unfold a03806
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03805.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha03792.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03795.pow 1)))

@[irreducible]
def a03807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a00785 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00265 ^ 1 * a00783 ^ 1)
theorem ha03807 : a03807.IsHomogeneous 174 := by
  unfold a03807
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a03808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a01852 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00289 ^ 1 * a00785 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a00785 ^ 1)
theorem ha03808 : a03808.IsHomogeneous 174 := by
  unfold a03808
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1)))

@[irreducible]
def a03809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03789 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03807 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03808 ^ 1)
theorem ha03809 : a03809.IsHomogeneous 180 := by
  unfold a03809
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03789.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03807.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03808.pow 1)))

@[irreducible]
def a03810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00288 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha03810 : a03810.IsHomogeneous 6 := by
  unfold a03810
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03810 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha03811 : a03811.IsHomogeneous 6 := by
  unfold a03811
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03812 : Poly := (C ((-1 : ℂ) / (466560 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00004 ^ 4 * a00005 ^ 4 * a00012 ^ 4) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00102 ^ 2 * a03811 ^ 1) + (C ((7 : ℂ) / (90 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 5 * a00005 ^ 3 * a00012 ^ 6) + (C ((7 : ℂ) / (108 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1)
theorem ha03812 : a03812.IsHomogeneous 56 := by
  unfold a03812
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (466560 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00004.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 4)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00102.pow 2)).mul (ha03811.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (90 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 5)).mul (ha00005.pow 3)).mul (ha00012.pow 6))).add (((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (108 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1)))

@[irreducible]
def a03813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a03812 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a01848 ^ 1)
theorem ha03813 : a03813.IsHomogeneous 118 := by
  unfold a03813
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03812.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha01848.pow 1)))

@[irreducible]
def a03814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a03813 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03807 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a03791 ^ 1)
theorem ha03814 : a03814.IsHomogeneous 180 := by
  unfold a03814
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03813.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03807.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha03791.pow 1)))

@[irreducible]
def a03815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03792 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03814 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03809 ^ 1)
theorem ha03815 : a03815.IsHomogeneous 186 := by
  unfold a03815
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03792.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03814.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03809.pow 1)))

@[irreducible]
def a03816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a01724 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00723 ^ 2)
theorem ha03816 : a03816.IsHomogeneous 108 := by
  unfold a03816
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha01724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00723.pow 2)))

@[irreducible]
def a03817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00105 ^ 1 * a03601 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00265 ^ 1 * a01724 ^ 1)
theorem ha03817 : a03817.IsHomogeneous 108 := by
  unfold a03817
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00105.pow 1)).mul (ha03601.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00265.pow 1)).mul (ha01724.pow 1)))

@[irreducible]
def a03818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03816 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a03817 ^ 1)
theorem ha03818 : a03818.IsHomogeneous 108 := by
  unfold a03818
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03816.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha03817.pow 1)))

@[irreducible]
def a03819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03816 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03818 ^ 1)
theorem ha03819 : a03819.IsHomogeneous 108 := by
  unfold a03819
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03816.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03818.pow 1)))

@[irreducible]
def a03820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a01852 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a03819 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00124 ^ 1 * a01852 ^ 1)
theorem ha03820 : a03820.IsHomogeneous 174 := by
  unfold a03820
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha03819.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00124.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a03821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03794 ^ 1) + (C ((16 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03808 ^ 1) + (C ((16 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03820 ^ 1)
theorem ha03821 : a03821.IsHomogeneous 180 := by
  unfold a03821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03794.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03808.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03820.pow 1)))

@[irreducible]
def a03822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03795 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03821 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03809 ^ 1)
theorem ha03822 : a03822.IsHomogeneous 186 := by
  unfold a03822
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03795.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03821.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03809.pow 1)))

@[irreducible]
def a03823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a03806 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03815 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03822 ^ 1)
theorem ha03823 : a03823.IsHomogeneous 192 := by
  unfold a03823
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha03806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03815.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03822.pow 1)))

@[irreducible]
def a03824 : Poly := (C ((-1 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a01855 ^ 1)
theorem ha03824 : a03824.IsHomogeneous 290 := by
  unfold a03824
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03823.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha01855.pow 1)))

@[irreducible]
def a03825 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03824 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03786 ^ 1)
theorem ha03825 : a03825.IsHomogeneous 388 := by
  unfold a03825
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03824.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03786.pow 1)))

@[irreducible]
def a03826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03788 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03825 ^ 1)
theorem ha03826 : a03826.IsHomogeneous 485 := by
  unfold a03826
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03788.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03825.pow 1)))

@[irreducible]
def a03827 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a01858 ^ 1)
theorem ha03827 : a03827.IsHomogeneous 388 := by
  unfold a03827
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha01858.pow 1)))

@[irreducible]
def a03828 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 2)
theorem ha03828 : a03828.IsHomogeneous 194 := by
  unfold a03828
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a03829 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a03828 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1)
theorem ha03829 : a03829.IsHomogeneous 194 := by
  unfold a03829
  exact (((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha03828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)))

@[irreducible]
def a03830 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00789 ^ 1)
theorem ha03830 : a03830.IsHomogeneous 291 := by
  unfold a03830
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00789.pow 1)))

@[irreducible]
def a03831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a03829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03830 ^ 1)
theorem ha03831 : a03831.IsHomogeneous 291 := by
  unfold a03831
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha03829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03830.pow 1)))

@[irreducible]
def a03832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a03831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a01858 ^ 1)
theorem ha03832 : a03832.IsHomogeneous 388 := by
  unfold a03832
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha03831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha01858.pow 1)))

@[irreducible]
def a03833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03832 ^ 1)
theorem ha03833 : a03833.IsHomogeneous 388 := by
  unfold a03833
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03832.pow 1)))

@[irreducible]
def a03834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01822 ^ 1) + (C ((25 : ℂ) / (144 : ℂ)) * a00773 ^ 2)
theorem ha03834 : a03834.IsHomogeneous 192 := by
  unfold a03834
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (144 : ℂ))).mul (ha00773.pow 2)))

@[irreducible]
def a03835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03764 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a01822 ^ 1)
theorem ha03835 : a03835.IsHomogeneous 192 := by
  unfold a03835
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03764.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a03836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03834 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a03835 ^ 1)
theorem ha03836 : a03836.IsHomogeneous 192 := by
  unfold a03836
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03834.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha03835.pow 1)))

@[irreducible]
def a03837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03834 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03836 ^ 1)
theorem ha03837 : a03837.IsHomogeneous 192 := by
  unfold a03837
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03834.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03836.pow 1)))

@[irreducible]
def a03838 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01861 ^ 1)
theorem ha03838 : a03838.IsHomogeneous 290 := by
  unfold a03838
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01861.pow 1)))

@[irreducible]
def a03839 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03838 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03827 ^ 1)
theorem ha03839 : a03839.IsHomogeneous 388 := by
  unfold a03839
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03838.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03827.pow 1)))

end CycleQ2Concrete
