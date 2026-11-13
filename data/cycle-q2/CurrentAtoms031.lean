import Proposal.CurrentAtoms030

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a09728 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a09722 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09727 ^ 1)
theorem ha09728 : a09728.IsHomogeneous 494 := by
  unfold a09728
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha09722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09727.pow 1)))

@[irreducible]
def a09729 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a09725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09728 ^ 1)
theorem ha09729 : a09729.IsHomogeneous 494 := by
  unfold a09729
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha09725.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09728.pow 1)))

@[irreducible]
def a09730 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01099 ^ 1 * a01949 ^ 1)
theorem ha09730 : a09730.IsHomogeneous 433 := by
  unfold a09730
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01099.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a09731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a05108 ^ 1)
theorem ha09731 : a09731.IsHomogeneous 373 := by
  unfold a09731
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha02533.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha05108.pow 1)))

@[irreducible]
def a09732 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09730 ^ 1)
theorem ha09732 : a09732.IsHomogeneous 433 := by
  unfold a09732
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09730.pow 1)))

@[irreducible]
def a09733 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00831 ^ 1)
theorem ha09733 : a09733.IsHomogeneous 96 := by
  unfold a09733
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a09734 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01327 ^ 1)
theorem ha09734 : a09734.IsHomogeneous 48 := by
  unfold a09734
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a09735 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00100 ^ 1 * a09734 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09733 ^ 1)
theorem ha09735 : a09735.IsHomogeneous 96 := by
  unfold a09735
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha09734.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09733.pow 1)))

@[irreducible]
def a09736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00506 ^ 1 * a00831 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a01941 ^ 1)
theorem ha09736 : a09736.IsHomogeneous 132 := by
  unfold a09736
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00506.pow 1)).mul (ha00831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a09737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09733 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09736 ^ 1)
theorem ha09737 : a09737.IsHomogeneous 132 := by
  unfold a09737
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09733.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09736.pow 1)))

@[irreducible]
def a09738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09737 ^ 1)
theorem ha09738 : a09738.IsHomogeneous 132 := by
  unfold a09738
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09737.pow 1)))

@[irreducible]
def a09739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01941 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03967 ^ 1)
theorem ha09739 : a09739.IsHomogeneous 132 := by
  unfold a09739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01941.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03967.pow 1)))

@[irreducible]
def a09740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09736 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a09739 ^ 1)
theorem ha09740 : a09740.IsHomogeneous 132 := by
  unfold a09740
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha09739.pow 1)))

@[irreducible]
def a09741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09737 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09740 ^ 1)
theorem ha09741 : a09741.IsHomogeneous 132 := by
  unfold a09741
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09737.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09740.pow 1)))

@[irreducible]
def a09742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09741 ^ 1)
theorem ha09742 : a09742.IsHomogeneous 132 := by
  unfold a09742
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09741.pow 1)))

@[irreducible]
def a09743 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00487 ^ 1 * a00864 ^ 1)
theorem ha09743 : a09743.IsHomogeneous 133 := by
  unfold a09743
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha01281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00487.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09744 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01281 ^ 1)
theorem ha09744 : a09744.IsHomogeneous 133 := by
  unfold a09744
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02847.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a09745 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a09744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09743 ^ 1)
theorem ha09745 : a09745.IsHomogeneous 133 := by
  unfold a09745
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha09744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09743.pow 1)))

@[irreducible]
def a09746 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00487 ^ 1 * a00864 ^ 1)
theorem ha09746 : a09746.IsHomogeneous 97 := by
  unfold a09746
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09746 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09743 ^ 1)
theorem ha09747 : a09747.IsHomogeneous 133 := by
  unfold a09747
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09743.pow 1)))

@[irreducible]
def a09748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09745 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09747 ^ 1)
theorem ha09748 : a09748.IsHomogeneous 133 := by
  unfold a09748
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09745.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09747.pow 1)))

@[irreducible]
def a09749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05610 ^ 1)
theorem ha09749 : a09749.IsHomogeneous 137 := by
  unfold a09749
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha02847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05610.pow 1)))

@[irreducible]
def a09750 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09749 ^ 1)
theorem ha09750 : a09750.IsHomogeneous 137 := by
  unfold a09750
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09749.pow 1)))

@[irreducible]
def a09751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09750 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a09745 ^ 1)
theorem ha09751 : a09751.IsHomogeneous 137 := by
  unfold a09751
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09750.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha09745.pow 1)))

@[irreducible]
def a09752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09751 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a09748 ^ 1)
theorem ha09752 : a09752.IsHomogeneous 137 := by
  unfold a09752
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09751.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha09748.pow 1)))

@[irreducible]
def a09753 : Poly := (C ((-4 : ℂ) / (75 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09752 ^ 1)
theorem ha09753 : a09753.IsHomogeneous 137 := by
  unfold a09753
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (75 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09742.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09752.pow 1)))

@[irreducible]
def a09754 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02530 ^ 1)
theorem ha09754 : a09754.IsHomogeneous 160 := by
  unfold a09754
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01097.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02530.pow 1)))

@[irreducible]
def a09755 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a02530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a05104 ^ 1)
theorem ha09755 : a09755.IsHomogeneous 166 := by
  unfold a09755
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha02530.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha05104.pow 1)))

@[irreducible]
def a09756 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09755 ^ 1)
theorem ha09756 : a09756.IsHomogeneous 166 := by
  unfold a09756
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09754.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09755.pow 1)))

@[irreducible]
def a09757 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00395 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01097 ^ 1)
theorem ha09757 : a09757.IsHomogeneous 154 := by
  unfold a09757
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00395.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a09758 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09757 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09754 ^ 1)
theorem ha09758 : a09758.IsHomogeneous 160 := by
  unfold a09758
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09754.pow 1)))

@[irreducible]
def a09759 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09758 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09756 ^ 1)
theorem ha09759 : a09759.IsHomogeneous 166 := by
  unfold a09759
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09758.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09756.pow 1)))

@[irreducible]
def a09760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01702 ^ 1)
theorem ha09760 : a09760.IsHomogeneous 148 := by
  unfold a09760
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09761 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a02520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05087 ^ 1)
theorem ha09761 : a09761.IsHomogeneous 149 := by
  unfold a09761
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha02520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05087.pow 1)))

@[irreducible]
def a09762 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a09760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09761 ^ 1)
theorem ha09762 : a09762.IsHomogeneous 149 := by
  unfold a09762
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha09760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09761.pow 1)))

@[irreducible]
def a09763 : Poly := (C ((-2 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00393 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01702 ^ 1)
theorem ha09763 : a09763.IsHomogeneous 148 := by
  unfold a09763
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00393.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09763 ^ 1)
theorem ha09764 : a09764.IsHomogeneous 148 := by
  unfold a09764
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09763.pow 1)))

@[irreducible]
def a09765 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a09764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09762 ^ 1)
theorem ha09765 : a09765.IsHomogeneous 149 := by
  unfold a09765
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha09764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09762.pow 1)))

@[irreducible]
def a09766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00637 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00260 ^ 1 * a01581 ^ 1)
theorem ha09766 : a09766.IsHomogeneous 100 := by
  unfold a09766
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00637.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00260.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00637 ^ 1 * a00712 ^ 1)
theorem ha09767 : a09767.IsHomogeneous 99 := by
  unfold a09767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00637.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a09768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09767 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09766 ^ 1)
theorem ha09768 : a09768.IsHomogeneous 100 := by
  unfold a09768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09766.pow 1)))

@[irreducible]
def a09769 : Poly := (C ((-81 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a01581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a03370 ^ 1)
theorem ha09769 : a09769.IsHomogeneous 100 := by
  unfold a09769
  exact ((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha01581.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03370.pow 1)))

@[irreducible]
def a09770 : Poly := (C ((-10 : ℂ) / (729 : ℂ)) * a09769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09766 ^ 1)
theorem ha09770 : a09770.IsHomogeneous 100 := by
  unfold a09770
  exact (((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (729 : ℂ))).mul (ha09769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09766.pow 1)))

@[irreducible]
def a09771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09768 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09770 ^ 1)
theorem ha09771 : a09771.IsHomogeneous 100 := by
  unfold a09771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09770.pow 1)))

@[irreducible]
def a09772 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00061 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01702 ^ 1)
theorem ha09772 : a09772.IsHomogeneous 99 := by
  unfold a09772
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09772 ^ 1)
theorem ha09773 : a09773.IsHomogeneous 99 := by
  unfold a09773
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09772.pow 1)))

@[irreducible]
def a09774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09768 ^ 1)
theorem ha09774 : a09774.IsHomogeneous 100 := by
  unfold a09774
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09768.pow 1)))

@[irreducible]
def a09775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09774 ^ 1)
theorem ha09775 : a09775.IsHomogeneous 100 := by
  unfold a09775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09774.pow 1)))

@[irreducible]
def a09776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 2) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00241 ^ 1 * a01678 ^ 1)
theorem ha09776 : a09776.IsHomogeneous 108 := by
  unfold a09776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09777 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00241 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a03534 ^ 1)
theorem ha09777 : a09777.IsHomogeneous 102 := by
  unfold a09777
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00241.pow 1)).mul (ha01678.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a09778 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a09776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09777 ^ 1)
theorem ha09778 : a09778.IsHomogeneous 108 := by
  unfold a09778
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha09776.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09777.pow 1)))

@[irreducible]
def a09779 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a09778 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09776 ^ 1)
theorem ha09779 : a09779.IsHomogeneous 108 := by
  unfold a09779
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha09778.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09776.pow 1)))

@[irreducible]
def a09780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09779 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09775 ^ 1)
theorem ha09780 : a09780.IsHomogeneous 113 := by
  unfold a09780
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09775.pow 1)))

@[irreducible]
def a09781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09780 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09775 ^ 1)
theorem ha09781 : a09781.IsHomogeneous 113 := by
  unfold a09781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09780.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09775.pow 1)))

@[irreducible]
def a09782 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09781 ^ 1)
theorem ha09782 : a09782.IsHomogeneous 149 := by
  unfold a09782
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09781.pow 1)))

@[irreducible]
def a09783 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a09782 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09761 ^ 1)
theorem ha09783 : a09783.IsHomogeneous 149 := by
  unfold a09783
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha09782.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09761.pow 1)))

@[irreducible]
def a09784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09783 ^ 1)
theorem ha09784 : a09784.IsHomogeneous 149 := by
  unfold a09784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09762.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09783.pow 1)))

@[irreducible]
def a09785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09765 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09784 ^ 1)
theorem ha09785 : a09785.IsHomogeneous 149 := by
  unfold a09785
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09784.pow 1)))

@[irreducible]
def a09786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01275 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00484 ^ 1 * a01678 ^ 1)
theorem ha09786 : a09786.IsHomogeneous 144 := by
  unfold a09786
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01275.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00484.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09787 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00691 ^ 1 * a01275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02837 ^ 1)
theorem ha09787 : a09787.IsHomogeneous 144 := by
  unfold a09787
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00691.pow 1)).mul (ha01275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02837.pow 1)))

@[irreducible]
def a09788 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09787 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09786 ^ 1)
theorem ha09788 : a09788.IsHomogeneous 144 := by
  unfold a09788
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09787.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09786.pow 1)))

@[irreducible]
def a09789 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a03534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01678 ^ 1)
theorem ha09789 : a09789.IsHomogeneous 138 := by
  unfold a09789
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a09790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09786 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09789 ^ 1)
theorem ha09790 : a09790.IsHomogeneous 144 := by
  unfold a09790
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09786.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09789.pow 1)))

@[irreducible]
def a09791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09788 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09790 ^ 1)
theorem ha09791 : a09791.IsHomogeneous 144 := by
  unfold a09791
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09788.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09790.pow 1)))

@[irreducible]
def a09792 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a05595 ^ 1)
theorem ha09792 : a09792.IsHomogeneous 144 := by
  unfold a09792
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a09793 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a09792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09787 ^ 1)
theorem ha09793 : a09793.IsHomogeneous 144 := by
  unfold a09793
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha09792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09787.pow 1)))

@[irreducible]
def a09794 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09788 ^ 1)
theorem ha09794 : a09794.IsHomogeneous 144 := by
  unfold a09794
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09788.pow 1)))

@[irreducible]
def a09795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09791 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09794 ^ 1)
theorem ha09795 : a09795.IsHomogeneous 144 := by
  unfold a09795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09791.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09794.pow 1)))

@[irreducible]
def a09796 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09795 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09785 ^ 1)
theorem ha09796 : a09796.IsHomogeneous 149 := by
  unfold a09796
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09795.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09785.pow 1)))

@[irreducible]
def a09797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a01581 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00637 ^ 1 * a00829 ^ 1)
theorem ha09797 : a09797.IsHomogeneous 136 := by
  unfold a09797
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00637.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a09798 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00211 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00637 ^ 1 * a00829 ^ 1)
theorem ha09798 : a09798.IsHomogeneous 136 := by
  unfold a09798
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00211.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00637.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a09799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09797 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09798 ^ 1)
theorem ha09799 : a09799.IsHomogeneous 136 := by
  unfold a09799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09798.pow 1)))

@[irreducible]
def a09800 : Poly := (C ((-2 : ℂ) / (81 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a03370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01581 ^ 1)
theorem ha09800 : a09800.IsHomogeneous 100 := by
  unfold a09800
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (81 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03370.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09800 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09797 ^ 1)
theorem ha09801 : a09801.IsHomogeneous 136 := by
  unfold a09801
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09800.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09797.pow 1)))

@[irreducible]
def a09802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09801 ^ 1)
theorem ha09802 : a09802.IsHomogeneous 136 := by
  unfold a09802
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09801.pow 1)))

@[irreducible]
def a09803 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a03963 ^ 1)
theorem ha09803 : a09803.IsHomogeneous 135 := by
  unfold a09803
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a09804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09798 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a09803 ^ 1)
theorem ha09804 : a09804.IsHomogeneous 136 := by
  unfold a09804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09798.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha09803.pow 1)))

@[irreducible]
def a09805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09799 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09804 ^ 1)
theorem ha09805 : a09805.IsHomogeneous 136 := by
  unfold a09805
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09804.pow 1)))

@[irreducible]
def a09806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09805 ^ 1)
theorem ha09806 : a09806.IsHomogeneous 136 := by
  unfold a09806
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09802.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09805.pow 1)))

@[irreducible]
def a09807 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09796 ^ 1)
theorem ha09807 : a09807.IsHomogeneous 149 := by
  unfold a09807
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09796.pow 1)))

@[irreducible]
def a09808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09807 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a05104 ^ 1)
theorem ha09808 : a09808.IsHomogeneous 173 := by
  unfold a09808
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09807.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha05104.pow 1)))

@[irreducible]
def a09809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09808 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09755 ^ 1)
theorem ha09809 : a09809.IsHomogeneous 173 := by
  unfold a09809
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09808.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09755.pow 1)))

@[irreducible]
def a09810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09809 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09756 ^ 1)
theorem ha09810 : a09810.IsHomogeneous 173 := by
  unfold a09810
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09756.pow 1)))

@[irreducible]
def a09811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09810 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09759 ^ 1)
theorem ha09811 : a09811.IsHomogeneous 173 := by
  unfold a09811
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09810.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09759.pow 1)))

@[irreducible]
def a09812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09811 ^ 1) + (C ((3 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a09753 ^ 1)
theorem ha09812 : a09812.IsHomogeneous 173 := by
  unfold a09812
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09811.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha09753.pow 1)))

@[irreducible]
def a09813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a05108 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09812 ^ 1)
theorem ha09813 : a09813.IsHomogeneous 283 := by
  unfold a09813
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha05108.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09812.pow 1)))

@[irreducible]
def a09814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09731 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a09813 ^ 1)
theorem ha09814 : a09814.IsHomogeneous 373 := by
  unfold a09814
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09731.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09813.pow 1)))

@[irreducible]
def a09815 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09814 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09732 ^ 1)
theorem ha09815 : a09815.IsHomogeneous 433 := by
  unfold a09815
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09814.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09732.pow 1)))

@[irreducible]
def a09816 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01099 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a03978 ^ 1)
theorem ha09816 : a09816.IsHomogeneous 457 := by
  unfold a09816
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01099.pow 1)).mul (ha01949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a09817 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09816 ^ 1)
theorem ha09817 : a09817.IsHomogeneous 457 := by
  unfold a09817
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09730.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09816.pow 1)))

@[irreducible]
def a09818 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09817 ^ 1)
theorem ha09818 : a09818.IsHomogeneous 457 := by
  unfold a09818
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09817.pow 1)))

@[irreducible]
def a09819 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09815 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09818 ^ 1)
theorem ha09819 : a09819.IsHomogeneous 457 := by
  unfold a09819
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09818.pow 1)))

@[irreducible]
def a09820 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09729 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a09819 ^ 1)
theorem ha09820 : a09820.IsHomogeneous 499 := by
  unfold a09820
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09729.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha09819.pow 1)))

@[irreducible]
def a09821 : Poly := (C ((-80 : ℂ) / (729 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00042 ^ 5 * a00100 ^ 5 * a09719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09820 ^ 1)
theorem ha09821 : a09821.IsHomogeneous 499 := by
  unfold a09821
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-80 : ℂ) / (729 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha09719.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09820.pow 1)))

@[irreducible]
def a09822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a05115 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a09821 ^ 1)
theorem ha09822 : a09822.IsHomogeneous 499 := by
  unfold a09822
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha05115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha09821.pow 1)))

@[irreducible]
def a09823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09822 ^ 1)
theorem ha09823 : a09823.IsHomogeneous 499 := by
  unfold a09823
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09822.pow 1)))

@[irreducible]
def a09824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09823 ^ 1)
theorem ha09824 : a09824.IsHomogeneous 499 := by
  unfold a09824
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09823.pow 1)))

@[irreducible]
def a09825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09460 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09824 ^ 1)
theorem ha09825 : a09825.IsHomogeneous 499 := by
  unfold a09825
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09460.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09824.pow 1)))

@[irreducible]
def a09826 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a05118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a09825 ^ 1)
theorem ha09826 : a09826.IsHomogeneous 925 := by
  unfold a09826
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha05118.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha09825.pow 1)))

@[irreducible]
def a09827 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09826 ^ 1)
theorem ha09827 : a09827.IsHomogeneous 1258 := by
  unfold a09827
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09450.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09826.pow 1)))

@[irreducible]
def a09828 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09827 ^ 1)
theorem ha09828 : a09828.IsHomogeneous 1591 := by
  unfold a09828
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09451.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09827.pow 1)))

@[irreducible]
def a09829 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09454 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09828 ^ 1)
theorem ha09829 : a09829.IsHomogeneous 1924 := by
  unfold a09829
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09454.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09828.pow 1)))

@[irreducible]
def a09830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02574 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a01118 ^ 1 * a01886 ^ 1)
theorem ha09830 : a09830.IsHomogeneous 1399 := by
  unfold a09830
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02574.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha01118.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a09831 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a02574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a05180 ^ 1)
theorem ha09831 : a09831.IsHomogeneous 1102 := by
  unfold a09831
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02574.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha05180.pow 1)))

@[irreducible]
def a09832 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09831 ^ 1)
theorem ha09832 : a09832.IsHomogeneous 1435 := by
  unfold a09832
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09830.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09831.pow 1)))

@[irreducible]
def a09833 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01118 ^ 1 * a01886 ^ 1)
theorem ha09833 : a09833.IsHomogeneous 1696 := by
  unfold a09833
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01118.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a09834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09830 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a09833 ^ 1)
theorem ha09834 : a09834.IsHomogeneous 1732 := by
  unfold a09834
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09830.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha09833.pow 1)))

@[irreducible]
def a09835 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09832 ^ 1)
theorem ha09835 : a09835.IsHomogeneous 1768 := by
  unfold a09835
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09834.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09832.pow 1)))

@[irreducible]
def a09836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02572 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a01117 ^ 1 * a01976 ^ 1)
theorem ha09836 : a09836.IsHomogeneous 343 := by
  unfold a09836
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02572.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha01117.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a09837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05177 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02572 ^ 1)
theorem ha09837 : a09837.IsHomogeneous 343 := by
  unfold a09837
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05177.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02572.pow 1)))

@[irreducible]
def a09838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09836 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a09837 ^ 1)
theorem ha09838 : a09838.IsHomogeneous 343 := by
  unfold a09838
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09836.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha09837.pow 1)))

@[irreducible]
def a09839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00404 ^ 1 * a04028 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01117 ^ 1 * a01976 ^ 1)
theorem ha09839 : a09839.IsHomogeneous 343 := by
  unfold a09839
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00404.pow 1)).mul (ha04028.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01117.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a09840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09836 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a09839 ^ 1)
theorem ha09840 : a09840.IsHomogeneous 343 := by
  unfold a09840
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09836.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha09839.pow 1)))

@[irreducible]
def a09841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09838 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09840 ^ 1)
theorem ha09841 : a09841.IsHomogeneous 343 := by
  unfold a09841
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09838.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09840.pow 1)))

@[irreducible]
def a09842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01112 ^ 1 * a01841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a02561 ^ 1)
theorem ha09842 : a09842.IsHomogeneous 91 := by
  unfold a09842
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01112.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha02561.pow 1)))

@[irreducible]
def a09843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02561 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a05158 ^ 1)
theorem ha09843 : a09843.IsHomogeneous 85 := by
  unfold a09843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02561.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha05158.pow 1)))

@[irreducible]
def a09844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09842 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09843 ^ 1)
theorem ha09844 : a09844.IsHomogeneous 91 := by
  unfold a09844
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09842.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09843.pow 1)))

@[irreducible]
def a09845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01107 ^ 1 * a01903 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00812 ^ 1 * a02551 ^ 1)
theorem ha09845 : a09845.IsHomogeneous 70 := by
  unfold a09845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01107.pow 1)).mul (ha01903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00812.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a09846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a02551 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00299 ^ 1 * a05141 ^ 1)
theorem ha09846 : a09846.IsHomogeneous 70 := by
  unfold a09846
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha02551.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00299.pow 1)).mul (ha05141.pow 1)))

@[irreducible]
def a09847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09845 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a09846 ^ 1)
theorem ha09847 : a09847.IsHomogeneous 70 := by
  unfold a09847
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09845.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha09846.pow 1)))

@[irreducible]
def a09848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01107 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00400 ^ 1 * a03811 ^ 1)
theorem ha09848 : a09848.IsHomogeneous 64 := by
  unfold a09848
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01107.pow 1)).mul (ha01903.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a09849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09848 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09845 ^ 1)
theorem ha09849 : a09849.IsHomogeneous 70 := by
  unfold a09849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09848.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09845.pow 1)))

@[irreducible]
def a09850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09849 ^ 1)
theorem ha09850 : a09850.IsHomogeneous 70 := by
  unfold a09850
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09849.pow 1)))

@[irreducible]
def a09851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01041 ^ 1 * a01896 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a02413 ^ 1)
theorem ha09851 : a09851.IsHomogeneous 45 := by
  unfold a09851
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01041.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00298 ^ 1 * a04894 ^ 1)
theorem ha09852 : a09852.IsHomogeneous 48 := by
  unfold a09852
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00298.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09851 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a09852 ^ 1)
theorem ha09853 : a09853.IsHomogeneous 48 := by
  unfold a09853
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09851.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha09852.pow 1)))

@[irreducible]
def a09854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a09471 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04894 ^ 1)
theorem ha09854 : a09854.IsHomogeneous 48 := by
  unfold a09854
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha09471.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09852 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a09854 ^ 1)
theorem ha09855 : a09855.IsHomogeneous 48 := by
  unfold a09855
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09852.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha09854.pow 1)))

@[irreducible]
def a09856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09853 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a09855 ^ 1)
theorem ha09856 : a09856.IsHomogeneous 48 := by
  unfold a09856
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09853.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha09855.pow 1)))

@[irreducible]
def a09857 : Poly := (C ((-7 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1 * a01896 ^ 1)
theorem ha09857 : a09857.IsHomogeneous 39 := by
  unfold a09857
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a09858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09851 ^ 1)
theorem ha09858 : a09858.IsHomogeneous 45 := by
  unfold a09858
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09857.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09851.pow 1)))

@[irreducible]
def a09859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09853 ^ 1)
theorem ha09859 : a09859.IsHomogeneous 48 := by
  unfold a09859
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09853.pow 1)))

@[irreducible]
def a09860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09859 ^ 1)
theorem ha09860 : a09860.IsHomogeneous 48 := by
  unfold a09860
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09859.pow 1)))

@[irreducible]
def a09861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02710 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a01207 ^ 2)
theorem ha09861 : a09861.IsHomogeneous 30 := by
  unfold a09861
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 2)))

@[irreducible]
def a09862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02710 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05389 ^ 1)
theorem ha09862 : a09862.IsHomogeneous 30 := by
  unfold a09862
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02710.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a09863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09862 ^ 1)
theorem ha09863 : a09863.IsHomogeneous 30 := by
  unfold a09863
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09861.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09862.pow 1)))

@[irreducible]
def a09864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09861 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a09863 ^ 1)
theorem ha09864 : a09864.IsHomogeneous 30 := by
  unfold a09864
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09861.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha09863.pow 1)))

@[irreducible]
def a09865 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09864 ^ 1)
theorem ha09865 : a09865.IsHomogeneous 53 := by
  unfold a09865
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09860.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09864.pow 1)))

@[irreducible]
def a09866 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a09860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09865 ^ 1)
theorem ha09866 : a09866.IsHomogeneous 53 := by
  unfold a09866
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha09860.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09865.pow 1)))

@[irreducible]
def a09867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a05141 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a09866 ^ 1)
theorem ha09867 : a09867.IsHomogeneous 71 := by
  unfold a09867
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha05141.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha09866.pow 1)))

@[irreducible]
def a09868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09846 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a09867 ^ 1)
theorem ha09868 : a09868.IsHomogeneous 71 := by
  unfold a09868
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha09867.pow 1)))

@[irreducible]
def a09869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09847 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a09868 ^ 1)
theorem ha09869 : a09869.IsHomogeneous 71 := by
  unfold a09869
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha09868.pow 1)))

@[irreducible]
def a09870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09869 ^ 1)
theorem ha09870 : a09870.IsHomogeneous 71 := by
  unfold a09870
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09850.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09869.pow 1)))

@[irreducible]
def a09871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01228 ^ 1 * a01298 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00494 ^ 1 * a02754 ^ 1)
theorem ha09871 : a09871.IsHomogeneous 63 := by
  unfold a09871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01228.pow 1)).mul (ha01298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a09872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01228 ^ 1 * a01298 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a02879 ^ 1)
theorem ha09872 : a09872.IsHomogeneous 69 := by
  unfold a09872
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01228.pow 1)).mul (ha01298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a09873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09872 ^ 1)
theorem ha09873 : a09873.IsHomogeneous 69 := by
  unfold a09873
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09871.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09872.pow 1)))

@[irreducible]
def a09874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a02754 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a03811 ^ 1)
theorem ha09874 : a09874.IsHomogeneous 57 := by
  unfold a09874
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha02754.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a09875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09871 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09874 ^ 1)
theorem ha09875 : a09875.IsHomogeneous 63 := by
  unfold a09875
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09871.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09874.pow 1)))

@[irreducible]
def a09876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09875 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09873 ^ 1)
theorem ha09876 : a09876.IsHomogeneous 69 := by
  unfold a09876
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09873.pow 1)))

@[irreducible]
def a09877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a05662 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a02879 ^ 1)
theorem ha09877 : a09877.IsHomogeneous 69 := by
  unfold a09877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha05662.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a09878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09872 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a09877 ^ 1)
theorem ha09878 : a09878.IsHomogeneous 69 := by
  unfold a09878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09872.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha09877.pow 1)))

@[irreducible]
def a09879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09878 ^ 1)
theorem ha09879 : a09879.IsHomogeneous 69 := by
  unfold a09879
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09873.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09878.pow 1)))

@[irreducible]
def a09880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09879 ^ 1)
theorem ha09880 : a09880.IsHomogeneous 69 := by
  unfold a09880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09876.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09879.pow 1)))

@[irreducible]
def a09881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a09870 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a09880 ^ 1)
theorem ha09881 : a09881.IsHomogeneous 77 := by
  unfold a09881
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha09870.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09880.pow 1)))

@[irreducible]
def a09882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01052 ^ 1 * a01962 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00841 ^ 1 * a02441 ^ 1)
theorem ha09882 : a09882.IsHomogeneous 77 := by
  unfold a09882
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01052.pow 1)).mul (ha01962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00841.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a09883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a00298 ^ 1 * a04950 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a02441 ^ 1)
theorem ha09883 : a09883.IsHomogeneous 77 := by
  unfold a09883
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha04950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a09884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09882 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a09883 ^ 1)
theorem ha09884 : a09884.IsHomogeneous 77 := by
  unfold a09884
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha09883.pow 1)))

@[irreducible]
def a09885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04950 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00126 ^ 1 * a09566 ^ 1)
theorem ha09885 : a09885.IsHomogeneous 43 := by
  unfold a09885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00126.pow 1)).mul (ha09566.pow 1)))

@[irreducible]
def a09886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a09885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09883 ^ 1)
theorem ha09886 : a09886.IsHomogeneous 77 := by
  unfold a09886
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha09885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09883.pow 1)))

@[irreducible]
def a09887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09884 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a09886 ^ 1)
theorem ha09887 : a09887.IsHomogeneous 77 := by
  unfold a09887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha09886.pow 1)))

@[irreducible]
def a09888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a04004 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a01052 ^ 1 * a01962 ^ 1)
theorem ha09888 : a09888.IsHomogeneous 76 := by
  unfold a09888
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha04004.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha01052.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a09889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09888 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a09882 ^ 1)
theorem ha09889 : a09889.IsHomogeneous 77 := by
  unfold a09889
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha09882.pow 1)))

@[irreducible]
def a09890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09884 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a09889 ^ 1)
theorem ha09890 : a09890.IsHomogeneous 77 := by
  unfold a09890
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha09889.pow 1)))

@[irreducible]
def a09891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09890 ^ 1)
theorem ha09891 : a09891.IsHomogeneous 77 := by
  unfold a09891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09890.pow 1)))

@[irreducible]
def a09892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09881 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a09891 ^ 1)
theorem ha09892 : a09892.IsHomogeneous 77 := by
  unfold a09892
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09881.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha09891.pow 1)))

@[irreducible]
def a09893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05158 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a09892 ^ 1)
theorem ha09893 : a09893.IsHomogeneous 83 := by
  unfold a09893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha09892.pow 1)))

@[irreducible]
def a09894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09843 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09893 ^ 1)
theorem ha09894 : a09894.IsHomogeneous 89 := by
  unfold a09894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09843.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09893.pow 1)))

@[irreducible]
def a09895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09844 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09894 ^ 1)
theorem ha09895 : a09895.IsHomogeneous 95 := by
  unfold a09895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09844.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09894.pow 1)))

@[irreducible]
def a09896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00402 ^ 1 * a03803 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01112 ^ 1 * a01841 ^ 1)
theorem ha09896 : a09896.IsHomogeneous 97 := by
  unfold a09896
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00402.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01112.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a09897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09896 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09842 ^ 1)
theorem ha09897 : a09897.IsHomogeneous 97 := by
  unfold a09897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09842.pow 1)))

@[irreducible]
def a09898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09897 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09844 ^ 1)
theorem ha09898 : a09898.IsHomogeneous 97 := by
  unfold a09898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09897.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09844.pow 1)))

@[irreducible]
def a09899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a09898 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09895 ^ 1)
theorem ha09899 : a09899.IsHomogeneous 101 := by
  unfold a09899
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha09898.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09895.pow 1)))

@[irreducible]
def a09900 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00501 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01275 ^ 1 * a01313 ^ 1)
theorem ha09900 : a09900.IsHomogeneous 302 := by
  unfold a09900
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01275.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a09901 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a01275 ^ 1 * a01313 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02904 ^ 1)
theorem ha09901 : a09901.IsHomogeneous 338 := by
  unfold a09901
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha01275.pow 1)).mul (ha01313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a09902 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09901 ^ 1)
theorem ha09902 : a09902.IsHomogeneous 338 := by
  unfold a09902
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09900.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09901.pow 1)))

@[irreducible]
def a09903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a05595 ^ 1)
theorem ha09903 : a09903.IsHomogeneous 264 := by
  unfold a09903
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha02837.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha05595.pow 1)))

@[irreducible]
def a09904 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a09903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09900 ^ 1)
theorem ha09904 : a09904.IsHomogeneous 302 := by
  unfold a09904
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha09903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09900.pow 1)))

@[irreducible]
def a09905 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09902 ^ 1)
theorem ha09905 : a09905.IsHomogeneous 338 := by
  unfold a09905
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09902.pow 1)))

@[irreducible]
def a09906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a05699 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00484 ^ 1 * a02904 ^ 1)
theorem ha09906 : a09906.IsHomogeneous 338 := by
  unfold a09906
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha05699.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00484.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a09907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09901 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a09906 ^ 1)
theorem ha09907 : a09907.IsHomogeneous 338 := by
  unfold a09907
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha09906.pow 1)))

@[irreducible]
def a09908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09902 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09907 ^ 1)
theorem ha09908 : a09908.IsHomogeneous 338 := by
  unfold a09908
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09907.pow 1)))

@[irreducible]
def a09909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09908 ^ 1)
theorem ha09909 : a09909.IsHomogeneous 338 := by
  unfold a09909
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09908.pow 1)))

@[irreducible]
def a09910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01979 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a02520 ^ 1)
theorem ha09910 : a09910.IsHomogeneous 301 := by
  unfold a09910
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01979.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09911 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a02520 ^ 1)
theorem ha09911 : a09911.IsHomogeneous 265 := by
  unfold a09911
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09910 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a09911 ^ 1)
theorem ha09912 : a09912.IsHomogeneous 301 := by
  unfold a09912
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09910.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha09911.pow 1)))

@[irreducible]
def a09913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a05087 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09781 ^ 1)
theorem ha09913 : a09913.IsHomogeneous 197 := by
  unfold a09913
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha05087.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09781.pow 1)))

@[irreducible]
def a09914 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a09913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09911 ^ 1)
theorem ha09914 : a09914.IsHomogeneous 265 := by
  unfold a09914
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09911.pow 1)))

@[irreducible]
def a09915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09912 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a09914 ^ 1)
theorem ha09915 : a09915.IsHomogeneous 301 := by
  unfold a09915
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09912.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha09914.pow 1)))

@[irreducible]
def a09916 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a01092 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a04032 ^ 1)
theorem ha09916 : a09916.IsHomogeneous 337 := by
  unfold a09916
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha01092.pow 1)).mul (ha01979.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a09917 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09910 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09916 ^ 1)
theorem ha09917 : a09917.IsHomogeneous 337 := by
  unfold a09917
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09910.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09916.pow 1)))

@[irreducible]
def a09918 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09917 ^ 1)
theorem ha09918 : a09918.IsHomogeneous 337 := by
  unfold a09918
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09917.pow 1)))

@[irreducible]
def a09919 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09915 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09918 ^ 1)
theorem ha09919 : a09919.IsHomogeneous 337 := by
  unfold a09919
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09915.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09918.pow 1)))

@[irreducible]
def a09920 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09909 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a09919 ^ 1)
theorem ha09920 : a09920.IsHomogeneous 343 := by
  unfold a09920
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09909.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha09919.pow 1)))

@[irreducible]
def a09921 : Poly := (C ((-1 : ℂ) / (6480 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00100 ^ 6 * a09899 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09920 ^ 1)
theorem ha09921 : a09921.IsHomogeneous 343 := by
  unfold a09921
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6480 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00100.pow 6)).mul (ha09899.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09920.pow 1)))

@[irreducible]
def a09922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05177 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a09921 ^ 1)
theorem ha09922 : a09922.IsHomogeneous 343 := by
  unfold a09922
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05177.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha09921.pow 1)))

@[irreducible]
def a09923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09922 ^ 1)
theorem ha09923 : a09923.IsHomogeneous 343 := by
  unfold a09923
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09837.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09922.pow 1)))

@[irreducible]
def a09924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09838 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a09923 ^ 1)
theorem ha09924 : a09924.IsHomogeneous 343 := by
  unfold a09924
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09838.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha09923.pow 1)))

@[irreducible]
def a09925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09924 ^ 1)
theorem ha09925 : a09925.IsHomogeneous 343 := by
  unfold a09925
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09924.pow 1)))

@[irreducible]
def a09926 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a09925 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a05180 ^ 1)
theorem ha09926 : a09926.IsHomogeneous 769 := by
  unfold a09926
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha09925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha05180.pow 1)))

@[irreducible]
def a09927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09926 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09831 ^ 1)
theorem ha09927 : a09927.IsHomogeneous 1102 := by
  unfold a09927
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09926.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09831.pow 1)))

@[irreducible]
def a09928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09832 ^ 1)
theorem ha09928 : a09928.IsHomogeneous 1435 := by
  unfold a09928
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09832.pow 1)))

@[irreducible]
def a09929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09928 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09835 ^ 1)
theorem ha09929 : a09929.IsHomogeneous 1768 := by
  unfold a09929
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09835.pow 1)))

@[irreducible]
def a09930 : Poly := (C ((-432 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 2 * a00100 ^ 1 * a09418 ^ 1) + (C ((-16 : ℂ) / (50625 : ℂ)) * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 6 * a00100 ^ 7 * a03873 ^ 1) + (C ((-8 : ℂ) / (9 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 6 * a09448 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a09829 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00042 ^ 1 * a09438 ^ 1) + (C ((128 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 6 * a00100 ^ 1 * a09428 ^ 1) + (C ((128 : ℂ) / (81 : ℂ)) * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 6 * a09929 ^ 1)
theorem ha09930 : a09930.IsHomogeneous 1936 := by
  unfold a09930
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha09418.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (50625 : ℂ))).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 6)).mul (ha00100.pow 7)).mul (ha03873.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha09448.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha09829.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00042.pow 1)).mul (ha09438.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((128 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 6)).mul (ha00100.pow 1)).mul (ha09428.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((128 : ℂ) / (81 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha09929.pow 1)))

@[irreducible]
def a09931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01180 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a02655 ^ 1)
theorem ha09931 : a09931.IsHomogeneous 1741 := by
  unfold a09931
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01180.pow 1)).mul (ha02046.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a09932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a02655 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a05296 ^ 1)
theorem ha09932 : a09932.IsHomogeneous 1324 := by
  unfold a09932
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha02655.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha05296.pow 1)))

@[irreducible]
def a09933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09931 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09932 ^ 1)
theorem ha09933 : a09933.IsHomogeneous 1741 := by
  unfold a09933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09931.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09932.pow 1)))

@[irreducible]
def a09934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02653 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01179 ^ 1 * a02038 ^ 1)
theorem ha09934 : a09934.IsHomogeneous 319 := by
  unfold a09934
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02653.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01179.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a09935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05293 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02653 ^ 1)
theorem ha09935 : a09935.IsHomogeneous 319 := by
  unfold a09935
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02653.pow 1)))

@[irreducible]
def a09936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09935 ^ 1)
theorem ha09936 : a09936.IsHomogeneous 319 := by
  unfold a09936
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09935.pow 1)))

@[irreducible]
def a09937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a04144 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a01179 ^ 1 * a02038 ^ 1)
theorem ha09937 : a09937.IsHomogeneous 319 := by
  unfold a09937
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha04144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha01179.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a09938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09934 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a09937 ^ 1)
theorem ha09938 : a09938.IsHomogeneous 319 := by
  unfold a09938
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha09937.pow 1)))

@[irreducible]
def a09939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09938 ^ 1)
theorem ha09939 : a09939.IsHomogeneous 319 := by
  unfold a09939
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09938.pow 1)))

@[irreducible]
def a09940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01041 ^ 1)
theorem ha09940 : a09940.IsHomogeneous 39 := by
  unfold a09940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha02413.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09941 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01041 ^ 1)
theorem ha09941 : a09941.IsHomogeneous 33 := by
  unfold a09941
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09942 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((-3 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01041 ^ 1)
theorem ha09942 : a09942.IsHomogeneous 33 := by
  unfold a09942
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09941 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09942 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a09940 ^ 1)
theorem ha09943 : a09943.IsHomogeneous 39 := by
  unfold a09943
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09941.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09942.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha09940.pow 1)))

@[irreducible]
def a09944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1)
theorem ha09944 : a09944.IsHomogeneous 42 := by
  unfold a09944
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00042 ^ 1 * a04894 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02413 ^ 1)
theorem ha09945 : a09945.IsHomogeneous 42 := by
  unfold a09945
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00042.pow 1)).mul (ha04894.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09944 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a09945 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09940 ^ 1)
theorem ha09946 : a09946.IsHomogeneous 42 := by
  unfold a09946
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09944.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha09945.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09940.pow 1)))

@[irreducible]
def a09947 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01041 ^ 1)
theorem ha09947 : a09947.IsHomogeneous 36 := by
  unfold a09947
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09944 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a09942 ^ 1)
theorem ha09948 : a09948.IsHomogeneous 42 := by
  unfold a09948
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09944.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha09942.pow 1)))

@[irreducible]
def a09949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09948 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09943 ^ 1)
theorem ha09949 : a09949.IsHomogeneous 42 := by
  unfold a09949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09948.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09943.pow 1)))

@[irreducible]
def a09950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a02413 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01041 ^ 1)
theorem ha09950 : a09950.IsHomogeneous 39 := by
  unfold a09950
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha02413.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02413 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a04894 ^ 1)
theorem ha09951 : a09951.IsHomogeneous 39 := by
  unfold a09951
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02413.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09940 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a09951 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a09950 ^ 1)
theorem ha09952 : a09952.IsHomogeneous 39 := by
  unfold a09952
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha09951.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha09950.pow 1)))

@[irreducible]
def a09953 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a00865 ^ 1) + (C ((-3 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00368 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01041 ^ 1)
theorem ha09953 : a09953.IsHomogeneous 33 := by
  unfold a09953
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09950 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09953 ^ 1)
theorem ha09954 : a09954.IsHomogeneous 39 := by
  unfold a09954
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09950.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09953.pow 1)))

@[irreducible]
def a09955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09954 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a09952 ^ 1)
theorem ha09955 : a09955.IsHomogeneous 39 := by
  unfold a09955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09954.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha09952.pow 1)))

@[irreducible]
def a09956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a04894 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a09471 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a04894 ^ 1)
theorem ha09956 : a09956.IsHomogeneous 42 := by
  unfold a09956
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha04894.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha09471.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09945 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a09956 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09951 ^ 1)
theorem ha09957 : a09957.IsHomogeneous 42 := by
  unfold a09957
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09945.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha09956.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09951.pow 1)))

@[irreducible]
def a09958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09946 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a09957 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09952 ^ 1)
theorem ha09958 : a09958.IsHomogeneous 42 := by
  unfold a09958
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha09957.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09952.pow 1)))

@[irreducible]
def a09959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09958 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a09955 ^ 1)
theorem ha09959 : a09959.IsHomogeneous 42 := by
  unfold a09959
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09958.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha09955.pow 1)))

@[irreducible]
def a09960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00455 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00455 ^ 1)
theorem ha09960 : a09960.IsHomogeneous 18 := by
  unfold a09960
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a09961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00455 ^ 1)
theorem ha09961 : a09961.IsHomogeneous 18 := by
  unfold a09961
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a09962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 1)
theorem ha09962 : a09962.IsHomogeneous 12 := by
  unfold a09962
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a09963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09960 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a09962 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a09961 ^ 1)
theorem ha09963 : a09963.IsHomogeneous 18 := by
  unfold a09963
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09960.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha09962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha09961.pow 1)))

@[irreducible]
def a09964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00455 ^ 1)
theorem ha09964 : a09964.IsHomogeneous 18 := by
  unfold a09964
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00455.pow 1)))

@[irreducible]
def a09965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02710 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01207 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1)
theorem ha09965 : a09965.IsHomogeneous 18 := by
  unfold a09965
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)))

@[irreducible]
def a09966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09964 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09965 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a09960 ^ 1)
theorem ha09966 : a09966.IsHomogeneous 24 := by
  unfold a09966
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09964.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09965.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha09960.pow 1)))

@[irreducible]
def a09967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1)
theorem ha09967 : a09967.IsHomogeneous 12 := by
  unfold a09967
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a09968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09964 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a09962 ^ 1)
theorem ha09968 : a09968.IsHomogeneous 18 := by
  unfold a09968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09964.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha09962.pow 1)))

@[irreducible]
def a09969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09968 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09966 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a09963 ^ 1)
theorem ha09969 : a09969.IsHomogeneous 24 := by
  unfold a09969
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09968.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09966.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha09963.pow 1)))

@[irreducible]
def a09970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00316 ^ 1 * a01207 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00455 ^ 1)
theorem ha09970 : a09970.IsHomogeneous 24 := by
  unfold a09970
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)).mul (ha01207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a09971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a02710 ^ 1)
theorem ha09971 : a09971.IsHomogeneous 18 := by
  unfold a09971
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01207.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha02710.pow 1)))

@[irreducible]
def a09972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09970 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09971 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a09960 ^ 1)
theorem ha09972 : a09972.IsHomogeneous 24 := by
  unfold a09972
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09971.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha09960.pow 1)))

@[irreducible]
def a09973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02007 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00864 ^ 1)
theorem ha09973 : a09973.IsHomogeneous 24 := by
  unfold a09973
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09973 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09961 ^ 1)
theorem ha09974 : a09974.IsHomogeneous 24 := by
  unfold a09974
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09973.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09961.pow 1)))

@[irreducible]
def a09975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09974 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a09963 ^ 1)
theorem ha09975 : a09975.IsHomogeneous 24 := by
  unfold a09975
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09974.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha09963.pow 1)))

@[irreducible]
def a09976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02710 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a05389 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a02710 ^ 1)
theorem ha09976 : a09976.IsHomogeneous 24 := by
  unfold a09976
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha05389.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha02710.pow 1)))

@[irreducible]
def a09977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09976 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a09971 ^ 1)
theorem ha09977 : a09977.IsHomogeneous 24 := by
  unfold a09977
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09965.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09976.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha09971.pow 1)))

@[irreducible]
def a09978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09966 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09977 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09972 ^ 1)
theorem ha09978 : a09978.IsHomogeneous 30 := by
  unfold a09978
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09966.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09977.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09972.pow 1)))

@[irreducible]
def a09979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09969 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09978 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09975 ^ 1)
theorem ha09979 : a09979.IsHomogeneous 30 := by
  unfold a09979
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09969.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09978.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09975.pow 1)))

@[irreducible]
def a09980 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a09959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09979 ^ 1)
theorem ha09980 : a09980.IsHomogeneous 49 := by
  unfold a09980
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha09959.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09979.pow 1)))

@[irreducible]
def a09981 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a09959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09980 ^ 1)
theorem ha09981 : a09981.IsHomogeneous 49 := by
  unfold a09981
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha09959.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09980.pow 1)))

@[irreducible]
def a09982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00809 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha09982 : a09982.IsHomogeneous 42 := by
  unfold a09982
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a09983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a01327 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha09983 : a09983.IsHomogeneous 42 := by
  unfold a09983
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

end CycleQ2Concrete
