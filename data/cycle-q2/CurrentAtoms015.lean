import Proposal.CurrentAtoms014

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a05632 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01313 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a01886 ^ 1)
theorem ha05632 : a05632.IsHomogeneous 1351 := by
  unfold a05632
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01313.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02904 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a01313 ^ 1)
theorem ha05633 : a05633.IsHomogeneous 1054 := by
  unfold a05633
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02904.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a05634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05633 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05632 ^ 1)
theorem ha05634 : a05634.IsHomogeneous 1387 := by
  unfold a05634
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05633.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05632.pow 1)))

@[irreducible]
def a05635 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a01886 ^ 1)
theorem ha05635 : a05635.IsHomogeneous 1648 := by
  unfold a05635
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05636 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05632 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a05635 ^ 1)
theorem ha05636 : a05636.IsHomogeneous 1684 := by
  unfold a05636
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05632.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha05635.pow 1)))

@[irreducible]
def a05637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05634 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05636 ^ 1)
theorem ha05637 : a05637.IsHomogeneous 1720 := by
  unfold a05637
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05634.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05636.pow 1)))

@[irreducible]
def a05638 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a01311 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00500 ^ 1 * a01976 ^ 1)
theorem ha05638 : a05638.IsHomogeneous 295 := by
  unfold a05638
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha01311.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a05639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a01311 ^ 1)
theorem ha05639 : a05639.IsHomogeneous 295 := by
  unfold a05639
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02901.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha01311.pow 1)))

@[irreducible]
def a05640 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a05639 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05638 ^ 1)
theorem ha05640 : a05640.IsHomogeneous 295 := by
  unfold a05640
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha05639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05638.pow 1)))

@[irreducible]
def a05641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a04028 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00500 ^ 1 * a01976 ^ 1)
theorem ha05641 : a05641.IsHomogeneous 295 := by
  unfold a05641
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha04028.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00500.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a05642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05638 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05641 ^ 1)
theorem ha05642 : a05642.IsHomogeneous 295 := by
  unfold a05642
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05641.pow 1)))

@[irreducible]
def a05643 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05640 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05642 ^ 1)
theorem ha05643 : a05643.IsHomogeneous 295 := by
  unfold a05643
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05640.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05642.pow 1)))

@[irreducible]
def a05644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00497 ^ 1 * a01841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01304 ^ 1)
theorem ha05644 : a05644.IsHomogeneous 90 := by
  unfold a05644
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00497.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01304.pow 1)))

@[irreducible]
def a05645 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01304 ^ 1)
theorem ha05645 : a05645.IsHomogeneous 84 := by
  unfold a05645
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01304.pow 1)))

@[irreducible]
def a05646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05644 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05645 ^ 1)
theorem ha05646 : a05646.IsHomogeneous 90 := by
  unfold a05646
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05644.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05645.pow 1)))

@[irreducible]
def a05647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01298 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00494 ^ 1 * a01903 ^ 1)
theorem ha05647 : a05647.IsHomogeneous 63 := by
  unfold a05647
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a05648 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a01298 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a02879 ^ 1)
theorem ha05648 : a05648.IsHomogeneous 69 := by
  unfold a05648
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha01298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a05649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05647 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05648 ^ 1)
theorem ha05649 : a05649.IsHomogeneous 69 := by
  unfold a05649
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05647.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05648.pow 1)))

@[irreducible]
def a05650 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a03811 ^ 1)
theorem ha05650 : a05650.IsHomogeneous 57 := by
  unfold a05650
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha01903.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a05651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05647 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a05650 ^ 1)
theorem ha05651 : a05651.IsHomogeneous 63 := by
  unfold a05651
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05647.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha05650.pow 1)))

@[irreducible]
def a05652 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05649 ^ 1)
theorem ha05652 : a05652.IsHomogeneous 69 := by
  unfold a05652
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05649.pow 1)))

@[irreducible]
def a05653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00809 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a01896 ^ 1)
theorem ha05653 : a05653.IsHomogeneous 45 := by
  unfold a05653
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00809.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a05654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02710 ^ 1)
theorem ha05654 : a05654.IsHomogeneous 48 := by
  unfold a05654
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05653 ^ 1)
theorem ha05655 : a05655.IsHomogeneous 51 := by
  unfold a05655
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05654.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05653.pow 1)))

@[irreducible]
def a05656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a05389 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00298 ^ 1 * a02710 ^ 1)
theorem ha05656 : a05656.IsHomogeneous 48 := by
  unfold a05656
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00298.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a05657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05654 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a05656 ^ 1)
theorem ha05657 : a05657.IsHomogeneous 48 := by
  unfold a05657
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha05656.pow 1)))

@[irreducible]
def a05658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05657 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05655 ^ 1)
theorem ha05658 : a05658.IsHomogeneous 51 := by
  unfold a05658
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05657.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05655.pow 1)))

@[irreducible]
def a05659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a03890 ^ 1)
theorem ha05659 : a05659.IsHomogeneous 39 := by
  unfold a05659
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01896.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a05660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05659 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05653 ^ 1)
theorem ha05660 : a05660.IsHomogeneous 45 := by
  unfold a05660
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05659.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05653.pow 1)))

@[irreducible]
def a05661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05655 ^ 1)
theorem ha05661 : a05661.IsHomogeneous 51 := by
  unfold a05661
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05655.pow 1)))

@[irreducible]
def a05662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05658 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05661 ^ 1)
theorem ha05662 : a05662.IsHomogeneous 51 := by
  unfold a05662
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05658.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05661.pow 1)))

@[irreducible]
def a05663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a05662 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a02879 ^ 1)
theorem ha05663 : a05663.IsHomogeneous 69 := by
  unfold a05663
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha05662.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a05664 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05648 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a05663 ^ 1)
theorem ha05664 : a05664.IsHomogeneous 69 := by
  unfold a05664
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05648.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha05663.pow 1)))

@[irreducible]
def a05665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05664 ^ 1)
theorem ha05665 : a05665.IsHomogeneous 69 := by
  unfold a05665
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05664.pow 1)))

@[irreducible]
def a05666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05652 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05665 ^ 1)
theorem ha05666 : a05666.IsHomogeneous 69 := by
  unfold a05666
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05652.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05665.pow 1)))

@[irreducible]
def a05667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a01228 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a01962 ^ 1)
theorem ha05667 : a05667.IsHomogeneous 75 := by
  unfold a05667
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha01228.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a05668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a02754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a01228 ^ 1)
theorem ha05668 : a05668.IsHomogeneous 75 := by
  unfold a05668
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha02754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a05669 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05667 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05668 ^ 1)
theorem ha05669 : a05669.IsHomogeneous 75 := by
  unfold a05669
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05668.pow 1)))

@[irreducible]
def a05670 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02754 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a03811 ^ 1)
theorem ha05670 : a05670.IsHomogeneous 45 := by
  unfold a05670
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a05671 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a05670 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05668 ^ 1)
theorem ha05671 : a05671.IsHomogeneous 75 := by
  unfold a05671
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha05670.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05668.pow 1)))

@[irreducible]
def a05672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05669 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05671 ^ 1)
theorem ha05672 : a05672.IsHomogeneous 75 := by
  unfold a05672
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05671.pow 1)))

@[irreducible]
def a05673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a04004 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a01962 ^ 1)
theorem ha05673 : a05673.IsHomogeneous 75 := by
  unfold a05673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha04004.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a05674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05667 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05673 ^ 1)
theorem ha05674 : a05674.IsHomogeneous 75 := by
  unfold a05674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05673.pow 1)))

@[irreducible]
def a05675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05674 ^ 1)
theorem ha05675 : a05675.IsHomogeneous 75 := by
  unfold a05675
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05674.pow 1)))

@[irreducible]
def a05676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05675 ^ 1)
theorem ha05676 : a05676.IsHomogeneous 75 := by
  unfold a05676
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05675.pow 1)))

@[irreducible]
def a05677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05666 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a05676 ^ 1)
theorem ha05677 : a05677.IsHomogeneous 75 := by
  unfold a05677
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05666.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha05676.pow 1)))

@[irreducible]
def a05678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05677 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a02889 ^ 1)
theorem ha05678 : a05678.IsHomogeneous 81 := by
  unfold a05678
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05677.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha02889.pow 1)))

@[irreducible]
def a05679 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05678 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a05645 ^ 1)
theorem ha05679 : a05679.IsHomogeneous 87 := by
  unfold a05679
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha05645.pow 1)))

@[irreducible]
def a05680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05679 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a05646 ^ 1)
theorem ha05680 : a05680.IsHomogeneous 93 := by
  unfold a05680
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05679.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha05646.pow 1)))

@[irreducible]
def a05681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00152 ^ 1 * a03803 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00497 ^ 1 * a01841 ^ 1)
theorem ha05681 : a05681.IsHomogeneous 96 := by
  unfold a05681
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00152.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00497.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a05682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05681 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05644 ^ 1)
theorem ha05682 : a05682.IsHomogeneous 96 := by
  unfold a05682
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05681.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05644.pow 1)))

@[irreducible]
def a05683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05682 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05646 ^ 1)
theorem ha05683 : a05683.IsHomogeneous 96 := by
  unfold a05683
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05682.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05646.pow 1)))

@[irreducible]
def a05684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05680 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a05683 ^ 1)
theorem ha05684 : a05684.IsHomogeneous 99 := by
  unfold a05684
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05680.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha05683.pow 1)))

@[irreducible]
def a05685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01979 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a01275 ^ 1)
theorem ha05685 : a05685.IsHomogeneous 289 := by
  unfold a05685
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01979.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05686 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a01275 ^ 1)
theorem ha05686 : a05686.IsHomogeneous 253 := by
  unfold a05686
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05685 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a05686 ^ 1)
theorem ha05687 : a05687.IsHomogeneous 289 := by
  unfold a05687
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05685.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha05686.pow 1)))

@[irreducible]
def a05688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05595 ^ 1)
theorem ha05688 : a05688.IsHomogeneous 185 := by
  unfold a05688
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha02837.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a05689 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a05688 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05686 ^ 1)
theorem ha05689 : a05689.IsHomogeneous 253 := by
  unfold a05689
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05688.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05686.pow 1)))

@[irreducible]
def a05690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05687 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a05689 ^ 1)
theorem ha05690 : a05690.IsHomogeneous 289 := by
  unfold a05690
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05687.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha05689.pow 1)))

@[irreducible]
def a05691 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00484 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04032 ^ 1)
theorem ha05691 : a05691.IsHomogeneous 289 := by
  unfold a05691
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00484.pow 1)).mul (ha01979.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a05692 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a05691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05685 ^ 1)
theorem ha05692 : a05692.IsHomogeneous 289 := by
  unfold a05692
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha05691.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05685.pow 1)))

@[irreducible]
def a05693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05692 ^ 1)
theorem ha05693 : a05693.IsHomogeneous 289 := by
  unfold a05693
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05692.pow 1)))

@[irreducible]
def a05694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05693 ^ 1)
theorem ha05694 : a05694.IsHomogeneous 289 := by
  unfold a05694
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05690.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05693.pow 1)))

@[irreducible]
def a05695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05694 ^ 1) + (C ((5 : ℂ) / (1296 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 5 * a05684 ^ 1)
theorem ha05695 : a05695.IsHomogeneous 295 := by
  unfold a05695
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05694.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1296 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 5)).mul (ha05684.pow 1)))

@[irreducible]
def a05696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02901 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05695 ^ 1)
theorem ha05696 : a05696.IsHomogeneous 295 := by
  unfold a05696
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05695.pow 1)))

@[irreducible]
def a05697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05639 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05696 ^ 1)
theorem ha05697 : a05697.IsHomogeneous 295 := by
  unfold a05697
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05696.pow 1)))

@[irreducible]
def a05698 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a05697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05640 ^ 1)
theorem ha05698 : a05698.IsHomogeneous 295 := by
  unfold a05698
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha05697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05640.pow 1)))

@[irreducible]
def a05699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05643 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05698 ^ 1)
theorem ha05699 : a05699.IsHomogeneous 295 := by
  unfold a05699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05643.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05698.pow 1)))

@[irreducible]
def a05700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a02904 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a05699 ^ 1)
theorem ha05700 : a05700.IsHomogeneous 721 := by
  unfold a05700
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha02904.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha05699.pow 1)))

@[irreducible]
def a05701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05700 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05633 ^ 1)
theorem ha05701 : a05701.IsHomogeneous 1054 := by
  unfold a05701
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05700.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05633.pow 1)))

@[irreducible]
def a05702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05634 ^ 1)
theorem ha05702 : a05702.IsHomogeneous 1387 := by
  unfold a05702
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05701.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05634.pow 1)))

@[irreducible]
def a05703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05637 ^ 1)
theorem ha05703 : a05703.IsHomogeneous 1720 := by
  unfold a05703
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05637.pow 1)))

@[irreducible]
def a05704 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 5 * a05367 ^ 1) + (C ((-3 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a05631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a05357 ^ 1) + (C ((64 : ℂ) / (243 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 5 * a05703 ^ 1)
theorem ha05704 : a05704.IsHomogeneous 1862 := by
  unfold a05704
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha05367.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha05631.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha05357.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (243 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha05703.pow 1)))

@[irreducible]
def a05705 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00853 ^ 1 * a02043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00881 ^ 1 * a01983 ^ 1)
theorem ha05705 : a05705.IsHomogeneous 1632 := by
  unfold a05705
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00853.pow 1)).mul (ha02043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00881.pow 1)).mul (ha01983.pow 1)))

@[irreducible]
def a05706 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a01983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a04037 ^ 1)
theorem ha05706 : a05706.IsHomogeneous 1929 := by
  unfold a05706
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha01983.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha04037.pow 1)))

@[irreducible]
def a05707 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05706 ^ 1)
theorem ha05707 : a05707.IsHomogeneous 1989 := by
  unfold a05707
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05706.pow 1)))

@[irreducible]
def a05708 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00312 ^ 1 * a04151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00853 ^ 1 * a02043 ^ 1)
theorem ha05708 : a05708.IsHomogeneous 1335 := by
  unfold a05708
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00312.pow 1)).mul (ha04151.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00853.pow 1)).mul (ha02043.pow 1)))

@[irreducible]
def a05709 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05708 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05705 ^ 1)
theorem ha05709 : a05709.IsHomogeneous 1692 := by
  unfold a05709
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05708.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05705.pow 1)))

@[irreducible]
def a05710 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a05707 ^ 1)
theorem ha05710 : a05710.IsHomogeneous 2049 := by
  unfold a05710
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05709.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha05707.pow 1)))

@[irreducible]
def a05711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01949 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a01886 ^ 1)
theorem ha05711 : a05711.IsHomogeneous 1416 := by
  unfold a05711
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01949.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05712 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a01886 ^ 1)
theorem ha05712 : a05712.IsHomogeneous 1689 := by
  unfold a05712
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05711 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05712 ^ 1)
theorem ha05713 : a05713.IsHomogeneous 1749 := by
  unfold a05713
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05711.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05712.pow 1)))

@[irreducible]
def a05714 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a03978 ^ 1)
theorem ha05714 : a05714.IsHomogeneous 1143 := by
  unfold a05714
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01949.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a05715 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05711 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05714 ^ 1)
theorem ha05715 : a05715.IsHomogeneous 1476 := by
  unfold a05715
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05711.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05714.pow 1)))

@[irreducible]
def a05716 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05715 ^ 1)
theorem ha05716 : a05716.IsHomogeneous 1809 := by
  unfold a05716
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05713.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05715.pow 1)))

@[irreducible]
def a05717 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a01883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00802 ^ 1 * a01707 ^ 1)
theorem ha05717 : a05717.IsHomogeneous 1158 := by
  unfold a05717
  exact (((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha01883.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00802.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a05718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00295 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00802 ^ 1 * a01707 ^ 1)
theorem ha05718 : a05718.IsHomogeneous 983 := by
  unfold a05718
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00295.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00802.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a05719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05718 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a05717 ^ 1)
theorem ha05719 : a05719.IsHomogeneous 1237 := by
  unfold a05719
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05718.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha05717.pow 1)))

@[irreducible]
def a05720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a01883 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a03869 ^ 1)
theorem ha05720 : a05720.IsHomogeneous 1333 := by
  unfold a05720
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha01883.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha03869.pow 1)))

@[irreducible]
def a05721 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05720 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05717 ^ 1)
theorem ha05721 : a05721.IsHomogeneous 1412 := by
  unfold a05721
  exact ((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05720.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05717.pow 1)))

@[irreducible]
def a05722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05719 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a05721 ^ 1)
theorem ha05722 : a05722.IsHomogeneous 1491 := by
  unfold a05722
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05719.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha05721.pow 1)))

@[irreducible]
def a05723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a02922 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01320 ^ 1 * a01705 ^ 1)
theorem ha05723 : a05723.IsHomogeneous 425 := by
  unfold a05723
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha02922.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01320.pow 1)).mul (ha01705.pow 1)))

@[irreducible]
def a05724 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a03566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01320 ^ 1 * a01705 ^ 1)
theorem ha05724 : a05724.IsHomogeneous 345 := by
  unfold a05724
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha03566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01320.pow 1)).mul (ha01705.pow 1)))

@[irreducible]
def a05725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05723 ^ 1) + (C ((64 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a05724 ^ 1)
theorem ha05725 : a05725.IsHomogeneous 425 := by
  unfold a05725
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05723.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha05724.pow 1)))

@[irreducible]
def a05726 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a02920 ^ 1)
theorem ha05726 : a05726.IsHomogeneous 340 := by
  unfold a05726
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha02920.pow 1)))

@[irreducible]
def a05727 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a03566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01705 ^ 1)
theorem ha05727 : a05727.IsHomogeneous 260 := by
  unfold a05727
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha03566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01705.pow 1)))

@[irreducible]
def a05728 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a05727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05726 ^ 1)
theorem ha05728 : a05728.IsHomogeneous 340 := by
  unfold a05728
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha05727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05726.pow 1)))

@[irreducible]
def a05729 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00714 ^ 1)
theorem ha05729 : a05729.IsHomogeneous 255 := by
  unfold a05729
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00714.pow 1)))

@[irreducible]
def a05730 : Poly := (C ((-1 : ℂ) / (64 : ℂ)) * a00714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 2)
theorem ha05730 : a05730.IsHomogeneous 170 := by
  unfold a05730
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (64 : ℂ))).mul (ha00714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a05731 : Poly := (C ((-64 : ℂ) / (1 : ℂ)) * a05730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1)
theorem ha05731 : a05731.IsHomogeneous 170 := by
  unfold a05731
  exact (((isHomogeneous_C (σ := Fin 6) ((-64 : ℂ) / (1 : ℂ))).mul (ha05730.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)))

@[irreducible]
def a05732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a05731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05729 ^ 1)
theorem ha05732 : a05732.IsHomogeneous 255 := by
  unfold a05732
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha05731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05729.pow 1)))

@[irreducible]
def a05733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a05732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a02920 ^ 1)
theorem ha05733 : a05733.IsHomogeneous 340 := by
  unfold a05733
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha05732.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha02920.pow 1)))

@[irreducible]
def a05734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05726 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05733 ^ 1)
theorem ha05734 : a05734.IsHomogeneous 340 := by
  unfold a05734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05733.pow 1)))

@[irreducible]
def a05735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05728 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05734 ^ 1)
theorem ha05735 : a05735.IsHomogeneous 340 := by
  unfold a05735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05728.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05734.pow 1)))

@[irreducible]
def a05736 : Poly := (C ((-5 : ℂ) / (256 : ℂ)) * a00714 ^ 1 * a02922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a05735 ^ 1)
theorem ha05736 : a05736.IsHomogeneous 425 := by
  unfold a05736
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (256 : ℂ))).mul (ha00714.pow 1)).mul (ha02922.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha05735.pow 1)))

@[irreducible]
def a05737 : Poly := (C ((-256 : ℂ) / (5 : ℂ)) * a05736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05723 ^ 1)
theorem ha05737 : a05737.IsHomogeneous 425 := by
  unfold a05737
  exact (((isHomogeneous_C (σ := Fin 6) ((-256 : ℂ) / (5 : ℂ))).mul (ha05736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05723.pow 1)))

@[irreducible]
def a05738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05737 ^ 1)
theorem ha05738 : a05738.IsHomogeneous 425 := by
  unfold a05738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05725.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05737.pow 1)))

@[irreducible]
def a05739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00261 ^ 1 * a03563 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a00713 ^ 1 * a01703 ^ 1)
theorem ha05739 : a05739.IsHomogeneous 179 := by
  unfold a05739
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00261.pow 1)).mul (ha03563.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha00713.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a05740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00713 ^ 1 * a01703 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a05739 ^ 1)
theorem ha05740 : a05740.IsHomogeneous 179 := by
  unfold a05740
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00713.pow 1)).mul (ha01703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha05739.pow 1)))

@[irreducible]
def a05741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01340 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00513 ^ 1 * a01327 ^ 1)
theorem ha05741 : a05741.IsHomogeneous 30 := by
  unfold a05741
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01340.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00513.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a05742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a02935 ^ 1)
theorem ha05742 : a05742.IsHomogeneous 24 := by
  unfold a05742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a05743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05741 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05742 ^ 1)
theorem ha05743 : a05743.IsHomogeneous 30 := by
  unfold a05743
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05741.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05742.pow 1)))

@[irreducible]
def a05744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02956 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a01340 ^ 1)
theorem ha05744 : a05744.IsHomogeneous 30 := by
  unfold a05744
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a05745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05741 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a05744 ^ 1)
theorem ha05745 : a05745.IsHomogeneous 30 := by
  unfold a05745
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05741.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha05744.pow 1)))

@[irreducible]
def a05746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05745 ^ 1)
theorem ha05746 : a05746.IsHomogeneous 30 := by
  unfold a05746
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05745.pow 1)))

@[irreducible]
def a05747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00132 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha05747 : a05747.IsHomogeneous 6 := by
  unfold a05747
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00132.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a05748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05747 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha05748 : a05748.IsHomogeneous 6 := by
  unfold a05748
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a05749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05748 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha05749 : a05749.IsHomogeneous 6 := by
  unfold a05749
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a05750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1)
theorem ha05750 : a05750.IsHomogeneous 6 := by
  unfold a05750
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)))

@[irreducible]
def a05751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02946 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05750 ^ 1)
theorem ha05751 : a05751.IsHomogeneous 6 := by
  unfold a05751
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05750.pow 1)))

@[irreducible]
def a05752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05751 ^ 1)
theorem ha05752 : a05752.IsHomogeneous 6 := by
  unfold a05752
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05751.pow 1)))

@[irreducible]
def a05753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02948 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05752 ^ 1)
theorem ha05753 : a05753.IsHomogeneous 6 := by
  unfold a05753
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02948.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05752.pow 1)))

@[irreducible]
def a05754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05753 ^ 1)
theorem ha05754 : a05754.IsHomogeneous 6 := by
  unfold a05754
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05753.pow 1)))

@[irreducible]
def a05755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a05754 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a02935 ^ 1)
theorem ha05755 : a05755.IsHomogeneous 18 := by
  unfold a05755
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha05754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a05756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05742 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a05755 ^ 1)
theorem ha05756 : a05756.IsHomogeneous 24 := by
  unfold a05756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05742.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha05755.pow 1)))

@[irreducible]
def a05757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05743 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05756 ^ 1)
theorem ha05757 : a05757.IsHomogeneous 30 := by
  unfold a05757
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05743.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05756.pow 1)))

@[irreducible]
def a05758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05746 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05757 ^ 1)
theorem ha05758 : a05758.IsHomogeneous 30 := by
  unfold a05758
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05757.pow 1)))

@[irreducible]
def a05759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00511 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01337 ^ 1)
theorem ha05759 : a05759.IsHomogeneous 18 := by
  unfold a05759
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01337.pow 1)))

@[irreducible]
def a05760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00511 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha05760 : a05760.IsHomogeneous 12 := by
  unfold a05760
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a05761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05759 ^ 1)
theorem ha05761 : a05761.IsHomogeneous 18 := by
  unfold a05761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05759.pow 1)))

@[irreducible]
def a05762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1)
theorem ha05762 : a05762.IsHomogeneous 6 := by
  unfold a05762
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a05763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05760 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05762 ^ 1)
theorem ha05763 : a05763.IsHomogeneous 12 := by
  unfold a05763
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05760.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05762.pow 1)))

@[irreducible]
def a05764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05763 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05761 ^ 1)
theorem ha05764 : a05764.IsHomogeneous 18 := by
  unfold a05764
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05761.pow 1)))

@[irreducible]
def a05765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02952 ^ 1)
theorem ha05765 : a05765.IsHomogeneous 18 := by
  unfold a05765
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02952.pow 1)))

@[irreducible]
def a05766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05759 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05765 ^ 1)
theorem ha05766 : a05766.IsHomogeneous 24 := by
  unfold a05766
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05759.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05765.pow 1)))

@[irreducible]
def a05767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05766 ^ 1)
theorem ha05767 : a05767.IsHomogeneous 24 := by
  unfold a05767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05761.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05766.pow 1)))

@[irreducible]
def a05768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05767 ^ 1)
theorem ha05768 : a05768.IsHomogeneous 24 := by
  unfold a05768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05767.pow 1)))

@[irreducible]
def a05769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a02949 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a01335 ^ 1)
theorem ha05769 : a05769.IsHomogeneous 18 := by
  unfold a05769
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha02949.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a05770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05769 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a01335 ^ 1)
theorem ha05770 : a05770.IsHomogeneous 18 := by
  unfold a05770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a05771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a05749 ^ 1)
theorem ha05771 : a05771.IsHomogeneous 6 := by
  unfold a05771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)))

@[irreducible]
def a05772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05771 ^ 1)
theorem ha05772 : a05772.IsHomogeneous 6 := by
  unfold a05772
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05771.pow 1)))

@[irreducible]
def a05773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05772 ^ 1)
theorem ha05773 : a05773.IsHomogeneous 6 := by
  unfold a05773
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05772.pow 1)))

@[irreducible]
def a05774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05773 ^ 1)
theorem ha05774 : a05774.IsHomogeneous 6 := by
  unfold a05774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05773.pow 1)))

@[irreducible]
def a05775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05774 ^ 1)
theorem ha05775 : a05775.IsHomogeneous 6 := by
  unfold a05775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05774.pow 1)))

@[irreducible]
def a05776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a02949 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05775 ^ 1)
theorem ha05776 : a05776.IsHomogeneous 12 := by
  unfold a05776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05775.pow 1)))

@[irreducible]
def a05777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05769 ^ 1)
theorem ha05777 : a05777.IsHomogeneous 18 := by
  unfold a05777
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05776.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05769.pow 1)))

@[irreducible]
def a05778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05777 ^ 1)
theorem ha05778 : a05778.IsHomogeneous 18 := by
  unfold a05778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05777.pow 1)))

@[irreducible]
def a05779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05770 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05778 ^ 1)
theorem ha05779 : a05779.IsHomogeneous 18 := by
  unfold a05779
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05778.pow 1)))

@[irreducible]
def a05780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a05779 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02952 ^ 1)
theorem ha05780 : a05780.IsHomogeneous 24 := by
  unfold a05780
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha05779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02952.pow 1)))

@[irreducible]
def a05781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05780 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05765 ^ 1)
theorem ha05781 : a05781.IsHomogeneous 24 := by
  unfold a05781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05780.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05765.pow 1)))

@[irreducible]
def a05782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05766 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a05781 ^ 1)
theorem ha05782 : a05782.IsHomogeneous 24 := by
  unfold a05782
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha05781.pow 1)))

@[irreducible]
def a05783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05782 ^ 1)
theorem ha05783 : a05783.IsHomogeneous 24 := by
  unfold a05783
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05782.pow 1)))

@[irreducible]
def a05784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05783 ^ 1)
theorem ha05784 : a05784.IsHomogeneous 24 := by
  unfold a05784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05783.pow 1)))

@[irreducible]
def a05785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02956 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05784 ^ 1)
theorem ha05785 : a05785.IsHomogeneous 30 := by
  unfold a05785
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05784.pow 1)))

@[irreducible]
def a05786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05785 ^ 1)
theorem ha05786 : a05786.IsHomogeneous 30 := by
  unfold a05786
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05785.pow 1)))

@[irreducible]
def a05787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05745 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a05786 ^ 1)
theorem ha05787 : a05787.IsHomogeneous 30 := by
  unfold a05787
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05745.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha05786.pow 1)))

@[irreducible]
def a05788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05746 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05787 ^ 1)
theorem ha05788 : a05788.IsHomogeneous 30 := by
  unfold a05788
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05787.pow 1)))

@[irreducible]
def a05789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05758 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05788 ^ 1)
theorem ha05789 : a05789.IsHomogeneous 30 := by
  unfold a05789
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05758.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05788.pow 1)))

@[irreducible]
def a05790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00316 ^ 1)
theorem ha05790 : a05790.IsHomogeneous 24 := by
  unfold a05790
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00520 ^ 1)
theorem ha05791 : a05791.IsHomogeneous 12 := by
  unfold a05791
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00316.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00520.pow 1)))

@[irreducible]
def a05792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00130 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00520 ^ 1)
theorem ha05792 : a05792.IsHomogeneous 24 := by
  unfold a05792
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a05793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05790 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a05792 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05791 ^ 1)
theorem ha05793 : a05793.IsHomogeneous 24 := by
  unfold a05793
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05790.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha05792.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05791.pow 1)))

@[irreducible]
def a05794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00316 ^ 1)
theorem ha05794 : a05794.IsHomogeneous 18 := by
  unfold a05794
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00864 ^ 1)
theorem ha05795 : a05795.IsHomogeneous 30 := by
  unfold a05795
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05795 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05790 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05794 ^ 1)
theorem ha05796 : a05796.IsHomogeneous 30 := by
  unfold a05796
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05795.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05790.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05794.pow 1)))

@[irreducible]
def a05797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha05797 : a05797.IsHomogeneous 12 := by
  unfold a05797
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a05798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05794 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05797 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05791 ^ 1)
theorem ha05798 : a05798.IsHomogeneous 18 := by
  unfold a05798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05794.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05797.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05791.pow 1)))

@[irreducible]
def a05799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05796 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05793 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05798 ^ 1)
theorem ha05799 : a05799.IsHomogeneous 30 := by
  unfold a05799
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05796.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05793.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05798.pow 1)))

@[irreducible]
def a05800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01356 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00520 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00520 ^ 1)
theorem ha05800 : a05800.IsHomogeneous 18 := by
  unfold a05800
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00520.pow 1)))

@[irreducible]
def a05801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha05801 : a05801.IsHomogeneous 12 := by
  unfold a05801
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a05802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05800 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05801 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05791 ^ 1)
theorem ha05802 : a05802.IsHomogeneous 18 := by
  unfold a05802
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05800.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05801.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05791.pow 1)))

@[irreducible]
def a05803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01356 ^ 1)
theorem ha05803 : a05803.IsHomogeneous 30 := by
  unfold a05803
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a05804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05803 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05800 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05792 ^ 1)
theorem ha05804 : a05804.IsHomogeneous 30 := by
  unfold a05804
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05800.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05792.pow 1)))

@[irreducible]
def a05805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05804 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05802 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05793 ^ 1)
theorem ha05805 : a05805.IsHomogeneous 30 := by
  unfold a05805
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05804.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05802.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05793.pow 1)))

@[irreducible]
def a05806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha05806 : a05806.IsHomogeneous 12 := by
  unfold a05806
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a05807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05806 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05797 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05801 ^ 1)
theorem ha05807 : a05807.IsHomogeneous 18 := by
  unfold a05807
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05797.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05801.pow 1)))

@[irreducible]
def a05808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05807 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05802 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05798 ^ 1)
theorem ha05808 : a05808.IsHomogeneous 24 := by
  unfold a05808
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05807.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05802.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05798.pow 1)))

@[irreducible]
def a05809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05799 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05805 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05808 ^ 1)
theorem ha05809 : a05809.IsHomogeneous 30 := by
  unfold a05809
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05805.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05808.pow 1)))

@[irreducible]
def a05810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a00520 ^ 1)
theorem ha05810 : a05810.IsHomogeneous 30 := by
  unfold a05810
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a05811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a02007 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00864 ^ 1)
theorem ha05811 : a05811.IsHomogeneous 30 := by
  unfold a05811
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05810 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05811 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a05790 ^ 1)
theorem ha05812 : a05812.IsHomogeneous 30 := by
  unfold a05812
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05811.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha05790.pow 1)))

@[irreducible]
def a05813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02985 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01356 ^ 1)
theorem ha05813 : a05813.IsHomogeneous 30 := by
  unfold a05813
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a05814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05810 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05813 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05792 ^ 1)
theorem ha05814 : a05814.IsHomogeneous 30 := by
  unfold a05814
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05813.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05792.pow 1)))

@[irreducible]
def a05815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05814 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a05793 ^ 1)
theorem ha05815 : a05815.IsHomogeneous 30 := by
  unfold a05815
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05812.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05814.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha05793.pow 1)))

@[irreducible]
def a05816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a04085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a02007 ^ 1)
theorem ha05816 : a05816.IsHomogeneous 30 := by
  unfold a05816
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a05817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05795 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a05816 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05811 ^ 1)
theorem ha05817 : a05817.IsHomogeneous 36 := by
  unfold a05817
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05795.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha05816.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05811.pow 1)))

@[irreducible]
def a05818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05796 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05817 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a05812 ^ 1)
theorem ha05818 : a05818.IsHomogeneous 36 := by
  unfold a05818
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05796.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05817.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha05812.pow 1)))

@[irreducible]
def a05819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05818 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a05815 ^ 1)
theorem ha05819 : a05819.IsHomogeneous 36 := by
  unfold a05819
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05818.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha05815.pow 1)))

@[irreducible]
def a05820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1)
theorem ha05820 : a05820.IsHomogeneous 12 := by
  unfold a05820
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)))

@[irreducible]
def a05821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha05821 : a05821.IsHomogeneous 6 := by
  unfold a05821
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a05822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05820 ^ 1)
theorem ha05822 : a05822.IsHomogeneous 12 := by
  unfold a05822
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05821.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05820.pow 1)))

@[irreducible]
def a05823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha05823 : a05823.IsHomogeneous 6 := by
  unfold a05823
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a05824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05823 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05821 ^ 1)
theorem ha05824 : a05824.IsHomogeneous 12 := by
  unfold a05824
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05823.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05821.pow 1)))

@[irreducible]
def a05825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05824 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05822 ^ 1)
theorem ha05825 : a05825.IsHomogeneous 18 := by
  unfold a05825
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05824.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05822.pow 1)))

@[irreducible]
def a05826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a02007 ^ 1)
theorem ha05826 : a05826.IsHomogeneous 12 := by
  unfold a05826
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha02007.pow 1)))

@[irreducible]
def a05827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05826 ^ 1)
theorem ha05827 : a05827.IsHomogeneous 12 := by
  unfold a05827
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05826.pow 1)))

@[irreducible]
def a05828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05822 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05827 ^ 1)
theorem ha05828 : a05828.IsHomogeneous 12 := by
  unfold a05828
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05827.pow 1)))

@[irreducible]
def a05829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05825 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05828 ^ 1)
theorem ha05829 : a05829.IsHomogeneous 18 := by
  unfold a05829
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05828.pow 1)))

@[irreducible]
def a05830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02007 ^ 1)
theorem ha05830 : a05830.IsHomogeneous 18 := by
  unfold a05830
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02007.pow 1)))

@[irreducible]
def a05831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05830 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05826 ^ 1)
theorem ha05831 : a05831.IsHomogeneous 18 := by
  unfold a05831
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05830.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05826.pow 1)))

@[irreducible]
def a05832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05831 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05827 ^ 1)
theorem ha05832 : a05832.IsHomogeneous 18 := by
  unfold a05832
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05827.pow 1)))

@[irreducible]
def a05833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05832 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05828 ^ 1)
theorem ha05833 : a05833.IsHomogeneous 18 := by
  unfold a05833
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05832.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05828.pow 1)))

@[irreducible]
def a05834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05829 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05833 ^ 1)
theorem ha05834 : a05834.IsHomogeneous 18 := by
  unfold a05834
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05833.pow 1)))

@[irreducible]
def a05835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05834 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a02985 ^ 1)
theorem ha05835 : a05835.IsHomogeneous 30 := by
  unfold a05835
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a05836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05803 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a05835 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05813 ^ 1)
theorem ha05836 : a05836.IsHomogeneous 36 := by
  unfold a05836
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05803.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha05835.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05813.pow 1)))

@[irreducible]
def a05837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05836 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05814 ^ 1)
theorem ha05837 : a05837.IsHomogeneous 36 := by
  unfold a05837
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05804.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05836.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05814.pow 1)))

@[irreducible]
def a05838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05837 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05815 ^ 1)
theorem ha05838 : a05838.IsHomogeneous 36 := by
  unfold a05838
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05805.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05837.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05815.pow 1)))

@[irreducible]
def a05839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05819 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05838 ^ 1)
theorem ha05839 : a05839.IsHomogeneous 36 := by
  unfold a05839
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05819.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05838.pow 1)))

@[irreducible]
def a05840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 2 * a05839 ^ 1) + (C ((8 : ℂ) / (405 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a05789 ^ 1)
theorem ha05840 : a05840.IsHomogeneous 48 := by
  unfold a05840
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 2)).mul (ha05839.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (405 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha05789.pow 1)))

@[irreducible]
def a05841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01373 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00528 ^ 1 * a01327 ^ 1)
theorem ha05841 : a05841.IsHomogeneous 36 := by
  unfold a05841
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01373.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00528.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a05842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00528 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a02935 ^ 1)
theorem ha05842 : a05842.IsHomogeneous 30 := by
  unfold a05842
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a05843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05842 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a05841 ^ 1)
theorem ha05843 : a05843.IsHomogeneous 36 := by
  unfold a05843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha05841.pow 1)))

@[irreducible]
def a05844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a03016 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01373 ^ 1)
theorem ha05844 : a05844.IsHomogeneous 36 := by
  unfold a05844
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a05845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05841 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05844 ^ 1)
theorem ha05845 : a05845.IsHomogeneous 36 := by
  unfold a05845
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05844.pow 1)))

@[irreducible]
def a05846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05843 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a05845 ^ 1)
theorem ha05846 : a05846.IsHomogeneous 36 := by
  unfold a05846
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05843.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha05845.pow 1)))

@[irreducible]
def a05847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a05754 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00161 ^ 1 * a02935 ^ 1)
theorem ha05847 : a05847.IsHomogeneous 24 := by
  unfold a05847
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00161.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a05848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05842 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05847 ^ 1)
theorem ha05848 : a05848.IsHomogeneous 30 := by
  unfold a05848
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05842.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05847.pow 1)))

@[irreducible]
def a05849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05848 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05843 ^ 1)
theorem ha05849 : a05849.IsHomogeneous 36 := by
  unfold a05849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05848.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05843.pow 1)))

@[irreducible]
def a05850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05846 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05849 ^ 1)
theorem ha05850 : a05850.IsHomogeneous 36 := by
  unfold a05850
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05849.pow 1)))

@[irreducible]
def a05851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha05851 : a05851.IsHomogeneous 12 := by
  unfold a05851
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a05852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha05852 : a05852.IsHomogeneous 12 := by
  unfold a05852
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a05853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05852 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05851 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02929 ^ 1)
theorem ha05853 : a05853.IsHomogeneous 18 := by
  unfold a05853
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05852.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05851.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02929.pow 1)))

@[irreducible]
def a05854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha05854 : a05854.IsHomogeneous 18 := by
  unfold a05854
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha05855 : a05855.IsHomogeneous 6 := by
  unfold a05855
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a05856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05851 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05854 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05855 ^ 1)
theorem ha05856 : a05856.IsHomogeneous 18 := by
  unfold a05856
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05851.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05854.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05855.pow 1)))

@[irreducible]
def a05857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02929 ^ 1)
theorem ha05857 : a05857.IsHomogeneous 12 := by
  unfold a05857
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05855.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02929.pow 1)))

@[irreducible]
def a05858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05853 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05856 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05857 ^ 1)
theorem ha05858 : a05858.IsHomogeneous 24 := by
  unfold a05858
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05853.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05856.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05857.pow 1)))

@[irreducible]
def a05859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1)
theorem ha05859 : a05859.IsHomogeneous 18 := by
  unfold a05859
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha05860 : a05860.IsHomogeneous 12 := by
  unfold a05860
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a05861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05851 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a05860 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05859 ^ 1)
theorem ha05861 : a05861.IsHomogeneous 18 := by
  unfold a05861
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05851.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha05860.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05859.pow 1)))

@[irreducible]
def a05862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha05862 : a05862.IsHomogeneous 12 := by
  unfold a05862
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a05863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05852 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a05862 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05860 ^ 1)
theorem ha05863 : a05863.IsHomogeneous 18 := by
  unfold a05863
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05852.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha05862.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05860.pow 1)))

@[irreducible]
def a05864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05863 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05861 ^ 1)
theorem ha05864 : a05864.IsHomogeneous 24 := by
  unfold a05864
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05853.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05863.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05861.pow 1)))

@[irreducible]
def a05865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a02007 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00864 ^ 1)
theorem ha05865 : a05865.IsHomogeneous 18 := by
  unfold a05865
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha02007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05854 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05859 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05865 ^ 1)
theorem ha05866 : a05866.IsHomogeneous 18 := by
  unfold a05866
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05854.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05859.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05865.pow 1)))

@[irreducible]
def a05867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05866 ^ 1)
theorem ha05867 : a05867.IsHomogeneous 18 := by
  unfold a05867
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05861.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05866.pow 1)))

@[irreducible]
def a05868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05864 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05867 ^ 1)
theorem ha05868 : a05868.IsHomogeneous 24 := by
  unfold a05868
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05864.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05867.pow 1)))

@[irreducible]
def a05869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha05869 : a05869.IsHomogeneous 18 := by
  unfold a05869
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00864 ^ 1)
theorem ha05870 : a05870.IsHomogeneous 24 := by
  unfold a05870
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05870 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05854 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a05869 ^ 1)
theorem ha05871 : a05871.IsHomogeneous 24 := by
  unfold a05871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05870.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05854.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha05869.pow 1)))

@[irreducible]
def a05872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha05872 : a05872.IsHomogeneous 12 := by
  unfold a05872
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a05873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05872 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05869 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05855 ^ 1)
theorem ha05873 : a05873.IsHomogeneous 18 := by
  unfold a05873
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05872.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05869.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05855.pow 1)))

@[irreducible]
def a05874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05871 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05856 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a05873 ^ 1)
theorem ha05874 : a05874.IsHomogeneous 24 := by
  unfold a05874
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05871.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05856.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha05873.pow 1)))

@[irreducible]
def a05875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha05875 : a05875.IsHomogeneous 12 := by
  unfold a05875
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a05876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05875 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02929 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05872 ^ 1)
theorem ha05876 : a05876.IsHomogeneous 18 := by
  unfold a05876
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05875.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02929.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05872.pow 1)))

@[irreducible]
def a05877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05876 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05857 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05873 ^ 1)
theorem ha05877 : a05877.IsHomogeneous 24 := by
  unfold a05877
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05876.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05857.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05873.pow 1)))

@[irreducible]
def a05878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05858 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05874 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a05877 ^ 1)
theorem ha05878 : a05878.IsHomogeneous 24 := by
  unfold a05878
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05874.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha05877.pow 1)))

@[irreducible]
def a05879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02007 ^ 1)
theorem ha05879 : a05879.IsHomogeneous 24 := by
  unfold a05879
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a05880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05870 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05879 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a05865 ^ 1)
theorem ha05880 : a05880.IsHomogeneous 24 := by
  unfold a05880
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05870.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05879.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha05865.pow 1)))

@[irreducible]
def a05881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05880 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05866 ^ 1)
theorem ha05881 : a05881.IsHomogeneous 24 := by
  unfold a05881
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05871.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05880.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05866.pow 1)))

@[irreducible]
def a05882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05874 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05881 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05867 ^ 1)
theorem ha05882 : a05882.IsHomogeneous 24 := by
  unfold a05882
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05874.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05881.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05867.pow 1)))

@[irreducible]
def a05883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05878 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05882 ^ 1)
theorem ha05883 : a05883.IsHomogeneous 24 := by
  unfold a05883
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05878.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05882.pow 1)))

@[irreducible]
def a05884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a03016 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a05883 ^ 1)
theorem ha05884 : a05884.IsHomogeneous 30 := by
  unfold a05884
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha05883.pow 1)))

@[irreducible]
def a05885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05844 ^ 1)
theorem ha05885 : a05885.IsHomogeneous 36 := by
  unfold a05885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05844.pow 1)))

@[irreducible]
def a05886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05845 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05885 ^ 1)
theorem ha05886 : a05886.IsHomogeneous 36 := by
  unfold a05886
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05845.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05885.pow 1)))

@[irreducible]
def a05887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05846 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a05886 ^ 1)
theorem ha05887 : a05887.IsHomogeneous 36 := by
  unfold a05887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha05886.pow 1)))

end CycleQ2Concrete
