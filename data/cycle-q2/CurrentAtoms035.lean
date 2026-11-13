import Proposal.CurrentAtoms034

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a10752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10738 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10751 ^ 1)
theorem ha10752 : a10752.IsHomogeneous 425 := by
  unfold a10752
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10751.pow 1)))

@[irreducible]
def a10753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a10752 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a05735 ^ 1)
theorem ha10753 : a10753.IsHomogeneous 510 := by
  unfold a10753
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha10752.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha05735.pow 1)))

@[irreducible]
def a10754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10728 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10753 ^ 1)
theorem ha10754 : a10754.IsHomogeneous 510 := by
  unfold a10754
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10728.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10753.pow 1)))

@[irreducible]
def a10755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10729 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10754 ^ 1)
theorem ha10755 : a10755.IsHomogeneous 510 := by
  unfold a10755
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10754.pow 1)))

@[irreducible]
def a10756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10755 ^ 1)
theorem ha10756 : a10756.IsHomogeneous 510 := by
  unfold a10756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10755.pow 1)))

@[irreducible]
def a10757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00713 ^ 1 * a03563 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01703 ^ 2)
theorem ha10757 : a10757.IsHomogeneous 178 := by
  unfold a10757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00713.pow 1)).mul (ha03563.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01703.pow 2)))

@[irreducible]
def a10758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00261 ^ 1 * a06726 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00713 ^ 1 * a03563 ^ 1)
theorem ha10758 : a10758.IsHomogeneous 178 := by
  unfold a10758
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00261.pow 1)).mul (ha06726.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00713.pow 1)).mul (ha03563.pow 1)))

@[irreducible]
def a10759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10757 ^ 1) + (C ((8 : ℂ) / (5 : ℂ)) * a10758 ^ 1)
theorem ha10759 : a10759.IsHomogeneous 178 := by
  unfold a10759
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (5 : ℂ))).mul (ha10758.pow 1)))

@[irreducible]
def a10760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10757 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10759 ^ 1)
theorem ha10760 : a10760.IsHomogeneous 178 := by
  unfold a10760
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10759.pow 1)))

@[irreducible]
def a10761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00513 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01327 ^ 1 * a01340 ^ 1)
theorem ha10761 : a10761.IsHomogeneous 30 := by
  unfold a10761
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00513.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a10762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a02956 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01327 ^ 1 * a01340 ^ 1)
theorem ha10762 : a10762.IsHomogeneous 36 := by
  unfold a10762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha02956.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01327.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a10763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10762 ^ 1)
theorem ha10763 : a10763.IsHomogeneous 36 := by
  unfold a10763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10761.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10762.pow 1)))

@[irreducible]
def a10764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a05754 ^ 1)
theorem ha10764 : a10764.IsHomogeneous 24 := by
  unfold a10764
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a10765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10761 ^ 1)
theorem ha10765 : a10765.IsHomogeneous 30 := by
  unfold a10765
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10761.pow 1)))

@[irreducible]
def a10766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10765 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10763 ^ 1)
theorem ha10766 : a10766.IsHomogeneous 36 := by
  unfold a10766
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10763.pow 1)))

@[irreducible]
def a10767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a05784 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a02956 ^ 1)
theorem ha10767 : a10767.IsHomogeneous 36 := by
  unfold a10767
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha05784.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha02956.pow 1)))

@[irreducible]
def a10768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10762 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10767 ^ 1)
theorem ha10768 : a10768.IsHomogeneous 36 := by
  unfold a10768
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10762.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10767.pow 1)))

@[irreducible]
def a10769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10763 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10768 ^ 1)
theorem ha10769 : a10769.IsHomogeneous 36 := by
  unfold a10769
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10768.pow 1)))

@[irreducible]
def a10770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10766 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10769 ^ 1)
theorem ha10770 : a10770.IsHomogeneous 36 := by
  unfold a10770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10769.pow 1)))

@[irreducible]
def a10771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((3 : ℂ) / (8 : ℂ)) * a00323 ^ 1)
theorem ha10771 : a10771.IsHomogeneous 6 := by
  unfold a10771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00323.pow 1)))

@[irreducible]
def a10772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((4 : ℂ) / (9 : ℂ)) * a10771 ^ 1)
theorem ha10772 : a10772.IsHomogeneous 6 := by
  unfold a10772
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha10771.pow 1)))

@[irreducible]
def a10773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (2 : ℂ)) * a10772 ^ 1)
theorem ha10773 : a10773.IsHomogeneous 6 := by
  unfold a10773
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10772.pow 1)))

@[irreducible]
def a10774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((126 : ℂ) / (1 : ℂ)) * a10773 ^ 1)
theorem ha10774 : a10774.IsHomogeneous 6 := by
  unfold a10774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((126 : ℂ) / (1 : ℂ))).mul (ha10773.pow 1)))

@[irreducible]
def a10775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05771 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a10774 ^ 1)
theorem ha10775 : a10775.IsHomogeneous 6 := by
  unfold a10775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha10774.pow 1)))

@[irreducible]
def a10776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05772 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10775 ^ 1)
theorem ha10776 : a10776.IsHomogeneous 6 := by
  unfold a10776
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05772.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10775.pow 1)))

@[irreducible]
def a10777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10776 ^ 1)
theorem ha10777 : a10777.IsHomogeneous 6 := by
  unfold a10777
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10776.pow 1)))

@[irreducible]
def a10778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05774 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10777 ^ 1)
theorem ha10778 : a10778.IsHomogeneous 6 := by
  unfold a10778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05774.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10777.pow 1)))

@[irreducible]
def a10779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10778 ^ 1)
theorem ha10779 : a10779.IsHomogeneous 6 := by
  unfold a10779
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10778.pow 1)))

@[irreducible]
def a10780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a10779 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a05754 ^ 1)
theorem ha10780 : a10780.IsHomogeneous 18 := by
  unfold a10780
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha10779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a10781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10764 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a10780 ^ 1)
theorem ha10781 : a10781.IsHomogeneous 24 := by
  unfold a10781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10764.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha10780.pow 1)))

@[irreducible]
def a10782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10781 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10765 ^ 1)
theorem ha10782 : a10782.IsHomogeneous 30 := by
  unfold a10782
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10781.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10765.pow 1)))

@[irreducible]
def a10783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10782 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10766 ^ 1)
theorem ha10783 : a10783.IsHomogeneous 36 := by
  unfold a10783
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10782.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10766.pow 1)))

@[irreducible]
def a10784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10783 ^ 1)
theorem ha10784 : a10784.IsHomogeneous 36 := by
  unfold a10784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10783.pow 1)))

@[irreducible]
def a10785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00511 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01337 ^ 1)
theorem ha10785 : a10785.IsHomogeneous 18 := by
  unfold a10785
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01337.pow 1)))

@[irreducible]
def a10786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01337 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a02952 ^ 1)
theorem ha10786 : a10786.IsHomogeneous 18 := by
  unfold a10786
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha02952.pow 1)))

@[irreducible]
def a10787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10785 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10786 ^ 1)
theorem ha10787 : a10787.IsHomogeneous 24 := by
  unfold a10787
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10785.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10786.pow 1)))

@[irreducible]
def a10788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00511 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha10788 : a10788.IsHomogeneous 12 := by
  unfold a10788
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a10789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10788 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10785 ^ 1)
theorem ha10789 : a10789.IsHomogeneous 18 := by
  unfold a10789
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10788.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10785.pow 1)))

@[irreducible]
def a10790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10787 ^ 1)
theorem ha10790 : a10790.IsHomogeneous 24 := by
  unfold a10790
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10787.pow 1)))

@[irreducible]
def a10791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00014 ^ 1)
theorem ha10791 : a10791.IsHomogeneous 6 := by
  unfold a10791
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a10792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10788 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10791 ^ 1)
theorem ha10792 : a10792.IsHomogeneous 12 := by
  unfold a10792
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10788.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10791.pow 1)))

@[irreducible]
def a10793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10789 ^ 1)
theorem ha10793 : a10793.IsHomogeneous 18 := by
  unfold a10793
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10789.pow 1)))

@[irreducible]
def a10794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10790 ^ 1)
theorem ha10794 : a10794.IsHomogeneous 24 := by
  unfold a10794
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10790.pow 1)))

@[irreducible]
def a10795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02952 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a05779 ^ 1)
theorem ha10795 : a10795.IsHomogeneous 18 := by
  unfold a10795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02952.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha05779.pow 1)))

@[irreducible]
def a10796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10786 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a10795 ^ 1)
theorem ha10796 : a10796.IsHomogeneous 18 := by
  unfold a10796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10786.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha10795.pow 1)))

@[irreducible]
def a10797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10787 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10796 ^ 1)
theorem ha10797 : a10797.IsHomogeneous 24 := by
  unfold a10797
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10787.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10796.pow 1)))

@[irreducible]
def a10798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10790 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10797 ^ 1)
theorem ha10798 : a10798.IsHomogeneous 24 := by
  unfold a10798
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10790.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10797.pow 1)))

@[irreducible]
def a10799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10794 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10798 ^ 1)
theorem ha10799 : a10799.IsHomogeneous 24 := by
  unfold a10799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10794.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10798.pow 1)))

@[irreducible]
def a10800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1 * a02949 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a01335 ^ 2)
theorem ha10800 : a10800.IsHomogeneous 12 := by
  unfold a10800
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).mul (ha02949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha01335.pow 2)))

@[irreducible]
def a10801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a05775 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a02949 ^ 1)
theorem ha10801 : a10801.IsHomogeneous 18 := by
  unfold a10801
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha05775.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a10802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10801 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a10800 ^ 1)
theorem ha10802 : a10802.IsHomogeneous 18 := by
  unfold a10802
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10801.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha10800.pow 1)))

@[irreducible]
def a10803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10802 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a10800 ^ 1)
theorem ha10803 : a10803.IsHomogeneous 18 := by
  unfold a10803
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10802.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha10800.pow 1)))

@[irreducible]
def a10804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((252 : ℂ) / (1 : ℂ)) * a10773 ^ 1)
theorem ha10804 : a10804.IsHomogeneous 6 := by
  unfold a10804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((252 : ℂ) / (1 : ℂ))).mul (ha10773.pow 1)))

@[irreducible]
def a10805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10804 ^ 1)
theorem ha10805 : a10805.IsHomogeneous 6 := by
  unfold a10805
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10804.pow 1)))

@[irreducible]
def a10806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10805 ^ 1)
theorem ha10806 : a10806.IsHomogeneous 6 := by
  unfold a10806
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10805.pow 1)))

@[irreducible]
def a10807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10806 ^ 1)
theorem ha10807 : a10807.IsHomogeneous 6 := by
  unfold a10807
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10806.pow 1)))

@[irreducible]
def a10808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10807 ^ 1)
theorem ha10808 : a10808.IsHomogeneous 6 := by
  unfold a10808
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10807.pow 1)))

@[irreducible]
def a10809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10808 ^ 1)
theorem ha10809 : a10809.IsHomogeneous 6 := by
  unfold a10809
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10808.pow 1)))

@[irreducible]
def a10810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a05775 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a10809 ^ 1)
theorem ha10810 : a10810.IsHomogeneous 12 := by
  unfold a10810
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha10809.pow 1)))

@[irreducible]
def a10811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10810 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10801 ^ 1)
theorem ha10811 : a10811.IsHomogeneous 18 := by
  unfold a10811
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10801.pow 1)))

@[irreducible]
def a10812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10811 ^ 1)
theorem ha10812 : a10812.IsHomogeneous 18 := by
  unfold a10812
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10802.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10811.pow 1)))

@[irreducible]
def a10813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10803 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10812 ^ 1)
theorem ha10813 : a10813.IsHomogeneous 18 := by
  unfold a10813
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10803.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10812.pow 1)))

@[irreducible]
def a10814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10803 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10813 ^ 1)
theorem ha10814 : a10814.IsHomogeneous 18 := by
  unfold a10814
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10803.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10813.pow 1)))

@[irreducible]
def a10815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a10814 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05779 ^ 1)
theorem ha10815 : a10815.IsHomogeneous 24 := by
  unfold a10815
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha10814.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05779.pow 1)))

@[irreducible]
def a10816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10815 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10795 ^ 1)
theorem ha10816 : a10816.IsHomogeneous 24 := by
  unfold a10816
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10815.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10795.pow 1)))

@[irreducible]
def a10817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10816 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10796 ^ 1)
theorem ha10817 : a10817.IsHomogeneous 24 := by
  unfold a10817
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10816.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10796.pow 1)))

@[irreducible]
def a10818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10797 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a10817 ^ 1)
theorem ha10818 : a10818.IsHomogeneous 24 := by
  unfold a10818
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha10817.pow 1)))

@[irreducible]
def a10819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10818 ^ 1)
theorem ha10819 : a10819.IsHomogeneous 24 := by
  unfold a10819
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10798.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10818.pow 1)))

@[irreducible]
def a10820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10819 ^ 1)
theorem ha10820 : a10820.IsHomogeneous 24 := by
  unfold a10820
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10819.pow 1)))

@[irreducible]
def a10821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a05784 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a10820 ^ 1)
theorem ha10821 : a10821.IsHomogeneous 30 := by
  unfold a10821
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha05784.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha10820.pow 1)))

@[irreducible]
def a10822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10767 ^ 1)
theorem ha10822 : a10822.IsHomogeneous 36 := by
  unfold a10822
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10821.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10767.pow 1)))

@[irreducible]
def a10823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10768 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10822 ^ 1)
theorem ha10823 : a10823.IsHomogeneous 36 := by
  unfold a10823
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10822.pow 1)))

@[irreducible]
def a10824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10823 ^ 1)
theorem ha10824 : a10824.IsHomogeneous 36 := by
  unfold a10824
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10823.pow 1)))

@[irreducible]
def a10825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10824 ^ 1)
theorem ha10825 : a10825.IsHomogeneous 36 := by
  unfold a10825
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10824.pow 1)))

@[irreducible]
def a10826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10784 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10825 ^ 1)
theorem ha10826 : a10826.IsHomogeneous 36 := by
  unfold a10826
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10784.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10825.pow 1)))

@[irreducible]
def a10827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00316 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00316 ^ 1 * a00520 ^ 1)
theorem ha10827 : a10827.IsHomogeneous 18 := by
  unfold a10827
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00316.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a10828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1 * a00864 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1 * a00520 ^ 1)
theorem ha10828 : a10828.IsHomogeneous 30 := by
  unfold a10828
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a10829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00864 ^ 1)
theorem ha10829 : a10829.IsHomogeneous 30 := by
  unfold a10829
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10828 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a10829 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10827 ^ 1)
theorem ha10830 : a10830.IsHomogeneous 30 := by
  unfold a10830
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha10829.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10827.pow 1)))

@[irreducible]
def a10831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a01356 ^ 1)
theorem ha10831 : a10831.IsHomogeneous 18 := by
  unfold a10831
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00520.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha01356.pow 1)))

@[irreducible]
def a10832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1)
theorem ha10832 : a10832.IsHomogeneous 12 := by
  unfold a10832
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)))

@[irreducible]
def a10833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10827 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10832 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a10831 ^ 1)
theorem ha10833 : a10833.IsHomogeneous 18 := by
  unfold a10833
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10827.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10832.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha10831.pow 1)))

@[irreducible]
def a10834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01356 ^ 1)
theorem ha10834 : a10834.IsHomogeneous 30 := by
  unfold a10834
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a10835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10828 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10834 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10831 ^ 1)
theorem ha10835 : a10835.IsHomogeneous 30 := by
  unfold a10835
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10831.pow 1)))

@[irreducible]
def a10836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10835 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10833 ^ 1)
theorem ha10836 : a10836.IsHomogeneous 30 := by
  unfold a10836
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10830.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10835.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10833.pow 1)))

@[irreducible]
def a10837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00316 ^ 1)
theorem ha10837 : a10837.IsHomogeneous 18 := by
  unfold a10837
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a10838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a02007 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00864 ^ 1)
theorem ha10838 : a10838.IsHomogeneous 24 := by
  unfold a10838
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10838 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a10827 ^ 1)
theorem ha10839 : a10839.IsHomogeneous 24 := by
  unfold a10839
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10837.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10838.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha10827.pow 1)))

@[irreducible]
def a10840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a02007 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a02007 ^ 1)
theorem ha10840 : a10840.IsHomogeneous 30 := by
  unfold a10840
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10840 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10829 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10838 ^ 1)
theorem ha10841 : a10841.IsHomogeneous 36 := by
  unfold a10841
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10840.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10829.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10838.pow 1)))

@[irreducible]
def a10842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10841 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10830 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10839 ^ 1)
theorem ha10842 : a10842.IsHomogeneous 36 := by
  unfold a10842
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10841.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10830.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10839.pow 1)))

@[irreducible]
def a10843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha10843 : a10843.IsHomogeneous 12 := by
  unfold a10843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a10844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10843 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10837 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10832 ^ 1)
theorem ha10844 : a10844.IsHomogeneous 18 := by
  unfold a10844
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10843.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10837.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10832.pow 1)))

@[irreducible]
def a10845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10844 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10839 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a10833 ^ 1)
theorem ha10845 : a10845.IsHomogeneous 24 := by
  unfold a10845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10844.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10839.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha10833.pow 1)))

@[irreducible]
def a10846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10842 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10836 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10845 ^ 1)
theorem ha10846 : a10846.IsHomogeneous 36 := by
  unfold a10846
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10842.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10836.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10845.pow 1)))

@[irreducible]
def a10847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00520 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00520 ^ 1)
theorem ha10847 : a10847.IsHomogeneous 18 := by
  unfold a10847
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00520.pow 1)))

@[irreducible]
def a10848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02985 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01356 ^ 1)
theorem ha10848 : a10848.IsHomogeneous 24 := by
  unfold a10848
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02985.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01356.pow 1)))

@[irreducible]
def a10849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10848 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10831 ^ 1)
theorem ha10849 : a10849.IsHomogeneous 24 := by
  unfold a10849
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10848.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10831.pow 1)))

@[irreducible]
def a10850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00520 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha10850 : a10850.IsHomogeneous 12 := by
  unfold a10850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a10851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10847 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10850 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10832 ^ 1)
theorem ha10851 : a10851.IsHomogeneous 18 := by
  unfold a10851
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10847.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10850.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10832.pow 1)))

@[irreducible]
def a10852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10851 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10849 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a10833 ^ 1)
theorem ha10852 : a10852.IsHomogeneous 24 := by
  unfold a10852
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10851.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10849.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha10833.pow 1)))

@[irreducible]
def a10853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05834 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02985 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a02985 ^ 1)
theorem ha10853 : a10853.IsHomogeneous 30 := by
  unfold a10853
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a10854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10853 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10834 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10848 ^ 1)
theorem ha10854 : a10854.IsHomogeneous 36 := by
  unfold a10854
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10853.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10848.pow 1)))

@[irreducible]
def a10855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10854 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10835 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10849 ^ 1)
theorem ha10855 : a10855.IsHomogeneous 36 := by
  unfold a10855
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10854.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10835.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10849.pow 1)))

@[irreducible]
def a10856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10855 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10836 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10852 ^ 1)
theorem ha10856 : a10856.IsHomogeneous 36 := by
  unfold a10856
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10855.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10836.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10852.pow 1)))

@[irreducible]
def a10857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha10857 : a10857.IsHomogeneous 12 := by
  unfold a10857
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a10858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10857 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10843 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10850 ^ 1)
theorem ha10858 : a10858.IsHomogeneous 18 := by
  unfold a10858
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10857.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10843.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10850.pow 1)))

@[irreducible]
def a10859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10858 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10851 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10844 ^ 1)
theorem ha10859 : a10859.IsHomogeneous 24 := by
  unfold a10859
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10858.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10851.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10844.pow 1)))

@[irreducible]
def a10860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10859 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10852 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10845 ^ 1)
theorem ha10860 : a10860.IsHomogeneous 30 := by
  unfold a10860
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10859.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10852.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10845.pow 1)))

@[irreducible]
def a10861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10846 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10856 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a10860 ^ 1)
theorem ha10861 : a10861.IsHomogeneous 36 := by
  unfold a10861
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10856.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha10860.pow 1)))

@[irreducible]
def a10862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00520 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00025 ^ 1 * a00864 ^ 1 * a01356 ^ 1)
theorem ha10862 : a10862.IsHomogeneous 36 := by
  unfold a10862
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a10863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a01356 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00864 ^ 1 * a01356 ^ 1)
theorem ha10863 : a10863.IsHomogeneous 36 := by
  unfold a10863
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha02985.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a10864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10828 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10863 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a10862 ^ 1)
theorem ha10864 : a10864.IsHomogeneous 36 := by
  unfold a10864
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10863.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha10862.pow 1)))

@[irreducible]
def a10865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a04085 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02007 ^ 1)
theorem ha10865 : a10865.IsHomogeneous 30 := by
  unfold a10865
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha04085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10829 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10862 ^ 1)
theorem ha10866 : a10866.IsHomogeneous 36 := by
  unfold a10866
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10829.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10865.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10862.pow 1)))

@[irreducible]
def a10867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a10866 ^ 1)
theorem ha10867 : a10867.IsHomogeneous 36 := by
  unfold a10867
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10830.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10864.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha10866.pow 1)))

@[irreducible]
def a10868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a02985 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05834 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1)
theorem ha10868 : a10868.IsHomogeneous 30 := by
  unfold a10868
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a10869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10834 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10868 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10863 ^ 1)
theorem ha10869 : a10869.IsHomogeneous 36 := by
  unfold a10869
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10834.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10868.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10863.pow 1)))

@[irreducible]
def a10870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10869 ^ 1)
theorem ha10870 : a10870.IsHomogeneous 36 := by
  unfold a10870
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10835.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10864.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10869.pow 1)))

@[irreducible]
def a10871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10870 ^ 1)
theorem ha10871 : a10871.IsHomogeneous 36 := by
  unfold a10871
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10836.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10867.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10870.pow 1)))

@[irreducible]
def a10872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a07557 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a04085 ^ 1)
theorem ha10872 : a10872.IsHomogeneous 30 := by
  unfold a10872
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha07557.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a10873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10840 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a10872 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10865 ^ 1)
theorem ha10873 : a10873.IsHomogeneous 36 := by
  unfold a10873
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10840.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha10872.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10865.pow 1)))

@[irreducible]
def a10874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10873 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10866 ^ 1)
theorem ha10874 : a10874.IsHomogeneous 42 := by
  unfold a10874
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10841.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10873.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10866.pow 1)))

@[irreducible]
def a10875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10842 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10874 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10867 ^ 1)
theorem ha10875 : a10875.IsHomogeneous 42 := by
  unfold a10875
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10874.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10867.pow 1)))

@[irreducible]
def a10876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10846 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10875 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10871 ^ 1)
theorem ha10876 : a10876.IsHomogeneous 42 := by
  unfold a10876
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10875.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10871.pow 1)))

@[irreducible]
def a10877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00864 ^ 1)
theorem ha10877 : a10877.IsHomogeneous 12 := by
  unfold a10877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00864.pow 1)))

@[irreducible]
def a10878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a02007 ^ 1)
theorem ha10878 : a10878.IsHomogeneous 12 := by
  unfold a10878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha02007.pow 1)))

@[irreducible]
def a10879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10877 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a10878 ^ 1)
theorem ha10879 : a10879.IsHomogeneous 12 := by
  unfold a10879
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10877.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha10878.pow 1)))

@[irreducible]
def a10880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha10880 : a10880.IsHomogeneous 6 := by
  unfold a10880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a10881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10877 ^ 1)
theorem ha10881 : a10881.IsHomogeneous 12 := by
  unfold a10881
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10877.pow 1)))

@[irreducible]
def a10882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10879 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10881 ^ 1)
theorem ha10882 : a10882.IsHomogeneous 12 := by
  unfold a10882
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10881.pow 1)))

@[irreducible]
def a10883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1)
theorem ha10883 : a10883.IsHomogeneous 6 := by
  unfold a10883
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a10884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10880 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a10883 ^ 1)
theorem ha10884 : a10884.IsHomogeneous 12 := by
  unfold a10884
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha10883.pow 1)))

@[irreducible]
def a10885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10881 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10884 ^ 1)
theorem ha10885 : a10885.IsHomogeneous 18 := by
  unfold a10885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10881.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10884.pow 1)))

@[irreducible]
def a10886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10882 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10885 ^ 1)
theorem ha10886 : a10886.IsHomogeneous 18 := by
  unfold a10886
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10885.pow 1)))

@[irreducible]
def a10887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02007 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a04085 ^ 1)
theorem ha10887 : a10887.IsHomogeneous 12 := by
  unfold a10887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha04085.pow 1)))

@[irreducible]
def a10888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10878 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a10887 ^ 1)
theorem ha10888 : a10888.IsHomogeneous 12 := by
  unfold a10888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha10887.pow 1)))

@[irreducible]
def a10889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10879 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a10888 ^ 1)
theorem ha10889 : a10889.IsHomogeneous 12 := by
  unfold a10889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha10888.pow 1)))

@[irreducible]
def a10890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10882 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10889 ^ 1)
theorem ha10890 : a10890.IsHomogeneous 12 := by
  unfold a10890
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10889.pow 1)))

@[irreducible]
def a10891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10886 ^ 1)
theorem ha10891 : a10891.IsHomogeneous 18 := by
  unfold a10891
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10886.pow 1)))

@[irreducible]
def a10892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04085 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07557 ^ 1)
theorem ha10892 : a10892.IsHomogeneous 18 := by
  unfold a10892
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07557.pow 1)))

@[irreducible]
def a10893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10887 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a10892 ^ 1)
theorem ha10893 : a10893.IsHomogeneous 18 := by
  unfold a10893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha10892.pow 1)))

@[irreducible]
def a10894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10888 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a10893 ^ 1)
theorem ha10894 : a10894.IsHomogeneous 18 := by
  unfold a10894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha10893.pow 1)))

@[irreducible]
def a10895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10889 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a10894 ^ 1)
theorem ha10895 : a10895.IsHomogeneous 18 := by
  unfold a10895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha10894.pow 1)))

@[irreducible]
def a10896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10895 ^ 1)
theorem ha10896 : a10896.IsHomogeneous 18 := by
  unfold a10896
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10895.pow 1)))

@[irreducible]
def a10897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10896 ^ 1)
theorem ha10897 : a10897.IsHomogeneous 18 := by
  unfold a10897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10896.pow 1)))

@[irreducible]
def a10898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a10897 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a05834 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05834 ^ 1)
theorem ha10898 : a10898.IsHomogeneous 30 := by
  unfold a10898
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha10897.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha05834.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05834.pow 1)))

@[irreducible]
def a10899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10853 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10868 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10898 ^ 1)
theorem ha10899 : a10899.IsHomogeneous 36 := by
  unfold a10899
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10853.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10868.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10898.pow 1)))

@[irreducible]
def a10900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10854 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10899 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10869 ^ 1)
theorem ha10900 : a10900.IsHomogeneous 42 := by
  unfold a10900
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10854.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10899.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10869.pow 1)))

@[irreducible]
def a10901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10900 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10870 ^ 1)
theorem ha10901 : a10901.IsHomogeneous 42 := by
  unfold a10901
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10855.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10900.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10870.pow 1)))

@[irreducible]
def a10902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10901 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10871 ^ 1)
theorem ha10902 : a10902.IsHomogeneous 42 := by
  unfold a10902
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10901.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10871.pow 1)))

@[irreducible]
def a10903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10876 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10902 ^ 1)
theorem ha10903 : a10903.IsHomogeneous 42 := by
  unfold a10903
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10861.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10876.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10902.pow 1)))

@[irreducible]
def a10904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 2 * a10903 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a10826 ^ 1)
theorem ha10904 : a10904.IsHomogeneous 54 := by
  unfold a10904
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 2)).mul (ha10903.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha10826.pow 1)))

@[irreducible]
def a10905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00528 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01327 ^ 1 * a01373 ^ 1)
theorem ha10905 : a10905.IsHomogeneous 30 := by
  unfold a10905
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00528.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01327.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a10906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a03016 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a01327 ^ 1 * a01373 ^ 1)
theorem ha10906 : a10906.IsHomogeneous 36 := by
  unfold a10906
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha03016.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a10907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10906 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a10905 ^ 1)
theorem ha10907 : a10907.IsHomogeneous 36 := by
  unfold a10907
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10906.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha10905.pow 1)))

@[irreducible]
def a10908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a05754 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00528 ^ 1 * a02935 ^ 1)
theorem ha10908 : a10908.IsHomogeneous 30 := by
  unfold a10908
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a10909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10908 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10905 ^ 1)
theorem ha10909 : a10909.IsHomogeneous 36 := by
  unfold a10909
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10908.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10905.pow 1)))

@[irreducible]
def a10910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10907 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10909 ^ 1)
theorem ha10910 : a10910.IsHomogeneous 36 := by
  unfold a10910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10909.pow 1)))

@[irreducible]
def a10911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a05883 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a03016 ^ 1)
theorem ha10911 : a10911.IsHomogeneous 36 := by
  unfold a10911
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha05883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha03016.pow 1)))

@[irreducible]
def a10912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10906 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10911 ^ 1)
theorem ha10912 : a10912.IsHomogeneous 36 := by
  unfold a10912
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10911.pow 1)))

@[irreducible]
def a10913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10912 ^ 1)
theorem ha10913 : a10913.IsHomogeneous 36 := by
  unfold a10913
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10912.pow 1)))

@[irreducible]
def a10914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10910 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10913 ^ 1)
theorem ha10914 : a10914.IsHomogeneous 36 := by
  unfold a10914
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10910.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10913.pow 1)))

@[irreducible]
def a10915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a10779 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a05754 ^ 1)
theorem ha10915 : a10915.IsHomogeneous 24 := by
  unfold a10915
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha10779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a10916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10908 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a10915 ^ 1)
theorem ha10916 : a10916.IsHomogeneous 30 := by
  unfold a10916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10908.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha10915.pow 1)))

@[irreducible]
def a10917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10909 ^ 1)
theorem ha10917 : a10917.IsHomogeneous 36 := by
  unfold a10917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10916.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10909.pow 1)))

@[irreducible]
def a10918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10910 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10917 ^ 1)
theorem ha10918 : a10918.IsHomogeneous 36 := by
  unfold a10918
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10910.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10917.pow 1)))

@[irreducible]
def a10919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10918 ^ 1)
theorem ha10919 : a10919.IsHomogeneous 36 := by
  unfold a10919
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10918.pow 1)))

@[irreducible]
def a10920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha10920 : a10920.IsHomogeneous 18 := by
  unfold a10920
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a10921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha10921 : a10921.IsHomogeneous 6 := by
  unfold a10921
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a10922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha10922 : a10922.IsHomogeneous 12 := by
  unfold a10922
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a10923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10920 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10921 ^ 1)
theorem ha10923 : a10923.IsHomogeneous 18 := by
  unfold a10923
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10922.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10920.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10921.pow 1)))

@[irreducible]
def a10924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 6)
theorem ha10924 : a10924.IsHomogeneous 6 := by
  unfold a10924
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a10925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10924 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10921 ^ 1)
theorem ha10925 : a10925.IsHomogeneous 12 := by
  unfold a10925
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10924.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10921.pow 1)))

@[irreducible]
def a10926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1)
theorem ha10926 : a10926.IsHomogeneous 12 := by
  unfold a10926
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)))

@[irreducible]
def a10927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10926 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10922 ^ 1) + (C ((28 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10924 ^ 1)
theorem ha10927 : a10927.IsHomogeneous 18 := by
  unfold a10927
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10922.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10924.pow 1)))

@[irreducible]
def a10928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10927 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10923 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10925 ^ 1)
theorem ha10928 : a10928.IsHomogeneous 24 := by
  unfold a10928
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10927.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10923.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10925.pow 1)))

@[irreducible]
def a10929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00864 ^ 1)
theorem ha10929 : a10929.IsHomogeneous 12 := by
  unfold a10929
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00864.pow 1)))

@[irreducible]
def a10930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00864 ^ 1)
theorem ha10930 : a10930.IsHomogeneous 18 := by
  unfold a10930
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00864.pow 1)))

@[irreducible]
def a10931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10930 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10929 ^ 1)
theorem ha10931 : a10931.IsHomogeneous 18 := by
  unfold a10931
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10930.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10929.pow 1)))

@[irreducible]
def a10932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10929 ^ 1)
theorem ha10932 : a10932.IsHomogeneous 12 := by
  unfold a10932
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10921.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10929.pow 1)))

@[irreducible]
def a10933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10931 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10932 ^ 1)
theorem ha10933 : a10933.IsHomogeneous 18 := by
  unfold a10933
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10923.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10931.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10932.pow 1)))

@[irreducible]
def a10934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10925 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10932 ^ 1)
theorem ha10934 : a10934.IsHomogeneous 18 := by
  unfold a10934
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10932.pow 1)))

@[irreducible]
def a10935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10928 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10933 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10934 ^ 1)
theorem ha10935 : a10935.IsHomogeneous 24 := by
  unfold a10935
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10928.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10933.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10934.pow 1)))

@[irreducible]
def a10936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00864 ^ 1)
theorem ha10936 : a10936.IsHomogeneous 18 := by
  unfold a10936
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a02007 ^ 1)
theorem ha10937 : a10937.IsHomogeneous 18 := by
  unfold a10937
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10920 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10937 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10936 ^ 1)
theorem ha10938 : a10938.IsHomogeneous 18 := by
  unfold a10938
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10937.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10936.pow 1)))

@[irreducible]
def a10939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha10939 : a10939.IsHomogeneous 12 := by
  unfold a10939
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a10940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10922 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10939 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10936 ^ 1)
theorem ha10940 : a10940.IsHomogeneous 18 := by
  unfold a10940
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10922.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10939.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10936.pow 1)))

@[irreducible]
def a10941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10940 ^ 1)
theorem ha10941 : a10941.IsHomogeneous 18 := by
  unfold a10941
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10923.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10938.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10940.pow 1)))

@[irreducible]
def a10942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha10942 : a10942.IsHomogeneous 12 := by
  unfold a10942
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a10943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10926 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a10942 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10939 ^ 1)
theorem ha10943 : a10943.IsHomogeneous 18 := by
  unfold a10943
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha10942.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10939.pow 1)))

@[irreducible]
def a10944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10943 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10940 ^ 1)
theorem ha10944 : a10944.IsHomogeneous 24 := by
  unfold a10944
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10927.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10943.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10940.pow 1)))

@[irreducible]
def a10945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10928 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10944 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10941 ^ 1)
theorem ha10945 : a10945.IsHomogeneous 24 := by
  unfold a10945
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10944.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10941.pow 1)))

@[irreducible]
def a10946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a04085 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a02007 ^ 1)
theorem ha10946 : a10946.IsHomogeneous 18 := by
  unfold a10946
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha04085.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10930 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10937 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10946 ^ 1)
theorem ha10947 : a10947.IsHomogeneous 18 := by
  unfold a10947
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10937.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10946.pow 1)))

@[irreducible]
def a10948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10947 ^ 1)
theorem ha10948 : a10948.IsHomogeneous 18 := by
  unfold a10948
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10938.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10947.pow 1)))

@[irreducible]
def a10949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10948 ^ 1)
theorem ha10949 : a10949.IsHomogeneous 18 := by
  unfold a10949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10933.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10941.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10948.pow 1)))

@[irreducible]
def a10950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10945 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10949 ^ 1)
theorem ha10950 : a10950.IsHomogeneous 24 := by
  unfold a10950
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10945.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10949.pow 1)))

@[irreducible]
def a10951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha10951 : a10951.IsHomogeneous 18 := by
  unfold a10951
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a10952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00864 ^ 1)
theorem ha10952 : a10952.IsHomogeneous 18 := by
  unfold a10952
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha02007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00864.pow 1)))

@[irreducible]
def a10953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10951 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10952 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10929 ^ 1)
theorem ha10953 : a10953.IsHomogeneous 18 := by
  unfold a10953
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10951.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10952.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10929.pow 1)))

@[irreducible]
def a10954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a04085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a02007 ^ 1)
theorem ha10954 : a10954.IsHomogeneous 24 := by
  unfold a10954
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10954 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10930 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a10952 ^ 1)
theorem ha10955 : a10955.IsHomogeneous 24 := by
  unfold a10955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10954.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10930.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha10952.pow 1)))

@[irreducible]
def a10956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10955 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10931 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a10953 ^ 1)
theorem ha10956 : a10956.IsHomogeneous 24 := by
  unfold a10956
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10955.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10931.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha10953.pow 1)))

@[irreducible]
def a10957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha10957 : a10957.IsHomogeneous 12 := by
  unfold a10957
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a10958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10951 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10921 ^ 1)
theorem ha10958 : a10958.IsHomogeneous 18 := by
  unfold a10958
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10951.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10921.pow 1)))

@[irreducible]
def a10959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10958 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10932 ^ 1)
theorem ha10959 : a10959.IsHomogeneous 18 := by
  unfold a10959
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10953.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10958.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10932.pow 1)))

@[irreducible]
def a10960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10956 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10933 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a10959 ^ 1)
theorem ha10960 : a10960.IsHomogeneous 24 := by
  unfold a10960
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10933.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha10959.pow 1)))

@[irreducible]
def a10961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha10961 : a10961.IsHomogeneous 12 := by
  unfold a10961
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a10962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10961 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10924 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10957 ^ 1)
theorem ha10962 : a10962.IsHomogeneous 18 := by
  unfold a10962
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10961.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10924.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10957.pow 1)))

@[irreducible]
def a10963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10962 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10958 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a10925 ^ 1)
theorem ha10963 : a10963.IsHomogeneous 24 := by
  unfold a10963
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10958.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha10925.pow 1)))

@[irreducible]
def a10964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10963 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10959 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10934 ^ 1)
theorem ha10964 : a10964.IsHomogeneous 24 := by
  unfold a10964
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10959.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10934.pow 1)))

@[irreducible]
def a10965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10935 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a10960 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a10964 ^ 1)
theorem ha10965 : a10965.IsHomogeneous 24 := by
  unfold a10965
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha10960.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha10964.pow 1)))

@[irreducible]
def a10966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a07557 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a04085 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a04085 ^ 1)
theorem ha10966 : a10966.IsHomogeneous 24 := by
  unfold a10966
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha07557.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha04085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a10967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10954 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a10966 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10946 ^ 1)
theorem ha10967 : a10967.IsHomogeneous 24 := by
  unfold a10967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10954.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha10966.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10946.pow 1)))

@[irreducible]
def a10968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10955 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10967 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10947 ^ 1)
theorem ha10968 : a10968.IsHomogeneous 24 := by
  unfold a10968
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10967.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10947.pow 1)))

@[irreducible]
def a10969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10956 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10968 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10948 ^ 1)
theorem ha10969 : a10969.IsHomogeneous 24 := by
  unfold a10969
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10956.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10968.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10948.pow 1)))

@[irreducible]
def a10970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10969 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a10949 ^ 1)
theorem ha10970 : a10970.IsHomogeneous 24 := by
  unfold a10970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10969.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha10949.pow 1)))

@[irreducible]
def a10971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10965 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a10970 ^ 1)
theorem ha10971 : a10971.IsHomogeneous 24 := by
  unfold a10971
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10965.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha10970.pow 1)))

@[irreducible]
def a10972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10971 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a05883 ^ 1)
theorem ha10972 : a10972.IsHomogeneous 30 := by
  unfold a10972
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10971.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha05883.pow 1)))

@[irreducible]
def a10973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10911 ^ 1)
theorem ha10973 : a10973.IsHomogeneous 36 := by
  unfold a10973
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10911.pow 1)))

@[irreducible]
def a10974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10912 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10973 ^ 1)
theorem ha10974 : a10974.IsHomogeneous 36 := by
  unfold a10974
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10973.pow 1)))

@[irreducible]
def a10975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10974 ^ 1)
theorem ha10975 : a10975.IsHomogeneous 36 := by
  unfold a10975
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10974.pow 1)))

@[irreducible]
def a10976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10975 ^ 1)
theorem ha10976 : a10976.IsHomogeneous 36 := by
  unfold a10976
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10975.pow 1)))

@[irreducible]
def a10977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10919 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10976 ^ 1)
theorem ha10977 : a10977.IsHomogeneous 36 := by
  unfold a10977
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10919.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10976.pow 1)))

@[irreducible]
def a10978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a02956 ^ 1) + (C ((16 : ℂ) / (5 : ℂ)) * a00864 ^ 1 * a01340 ^ 1)
theorem ha10978 : a10978.IsHomogeneous 30 := by
  unfold a10978
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha02956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (5 : ℂ))).mul (ha00864.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a10979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00513 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00864 ^ 1 * a01340 ^ 1)
theorem ha10979 : a10979.IsHomogeneous 36 := by
  unfold a10979
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00513.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00864.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a10980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10979 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a10978 ^ 1)
theorem ha10980 : a10980.IsHomogeneous 36 := by
  unfold a10980
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10979.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha10978.pow 1)))

@[irreducible]
def a10981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a04085 ^ 1)
theorem ha10981 : a10981.IsHomogeneous 30 := by
  unfold a10981
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a10982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10981 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10979 ^ 1)
theorem ha10982 : a10982.IsHomogeneous 36 := by
  unfold a10982
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10979.pow 1)))

@[irreducible]
def a10983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10980 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10982 ^ 1)
theorem ha10983 : a10983.IsHomogeneous 36 := by
  unfold a10983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10980.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10982.pow 1)))

@[irreducible]
def a10984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a02956 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a05784 ^ 1)
theorem ha10984 : a10984.IsHomogeneous 30 := by
  unfold a10984
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha02956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha05784.pow 1)))

@[irreducible]
def a10985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10984 ^ 1)
theorem ha10985 : a10985.IsHomogeneous 30 := by
  unfold a10985
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10978.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10984.pow 1)))

@[irreducible]
def a10986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10980 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a10985 ^ 1)
theorem ha10986 : a10986.IsHomogeneous 36 := by
  unfold a10986
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10980.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha10985.pow 1)))

@[irreducible]
def a10987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10986 ^ 1)
theorem ha10987 : a10987.IsHomogeneous 36 := by
  unfold a10987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10983.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10986.pow 1)))

@[irreducible]
def a10988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a07557 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00157 ^ 1 * a04085 ^ 1)
theorem ha10988 : a10988.IsHomogeneous 24 := by
  unfold a10988
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha07557.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00157.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a10989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10981 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a10988 ^ 1)
theorem ha10989 : a10989.IsHomogeneous 30 := by
  unfold a10989
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10981.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha10988.pow 1)))

@[irreducible]
def a10990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10989 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10982 ^ 1)
theorem ha10990 : a10990.IsHomogeneous 36 := by
  unfold a10990
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10989.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10982.pow 1)))

@[irreducible]
def a10991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10990 ^ 1)
theorem ha10991 : a10991.IsHomogeneous 36 := by
  unfold a10991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10983.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10990.pow 1)))

@[irreducible]
def a10992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10987 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10991 ^ 1)
theorem ha10992 : a10992.IsHomogeneous 36 := by
  unfold a10992
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10987.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10991.pow 1)))

@[irreducible]
def a10993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10820 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05784 ^ 1)
theorem ha10993 : a10993.IsHomogeneous 30 := by
  unfold a10993
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10820.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05784.pow 1)))

@[irreducible]
def a10994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10993 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10984 ^ 1)
theorem ha10994 : a10994.IsHomogeneous 36 := by
  unfold a10994
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10993.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10984.pow 1)))

@[irreducible]
def a10995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10994 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a10985 ^ 1)
theorem ha10995 : a10995.IsHomogeneous 36 := by
  unfold a10995
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10994.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha10985.pow 1)))

@[irreducible]
def a10996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10986 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a10995 ^ 1)
theorem ha10996 : a10996.IsHomogeneous 36 := by
  unfold a10996
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10986.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha10995.pow 1)))

@[irreducible]
def a10997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10987 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10996 ^ 1)
theorem ha10997 : a10997.IsHomogeneous 36 := by
  unfold a10997
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10987.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10996.pow 1)))

@[irreducible]
def a10998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10997 ^ 1)
theorem ha10998 : a10998.IsHomogeneous 36 := by
  unfold a10998
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10992.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10997.pow 1)))

@[irreducible]
def a10999 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a10977 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a10998 ^ 1)
theorem ha10999 : a10999.IsHomogeneous 49 := by
  unfold a10999
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha10977.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha10998.pow 1)))

@[irreducible]
def a11000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a01327 ^ 1)
theorem ha11000 : a11000.IsHomogeneous 24 := by
  unfold a11000
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1 * a01327 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00506 ^ 1 * a00520 ^ 1)
theorem ha11001 : a11001.IsHomogeneous 36 := by
  unfold a11001
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01356.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a11002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a01327 ^ 1)
theorem ha11002 : a11002.IsHomogeneous 24 := by
  unfold a11002
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11001 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11002 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11000 ^ 1)
theorem ha11003 : a11003.IsHomogeneous 36 := by
  unfold a11003
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11001.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11002.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11000.pow 1)))

@[irreducible]
def a11004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01356 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00520 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00520 ^ 1)
theorem ha11004 : a11004.IsHomogeneous 24 := by
  unfold a11004
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a11005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00155 ^ 1 * a00520 ^ 1)
theorem ha11005 : a11005.IsHomogeneous 18 := by
  unfold a11005
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00155.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a11006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11000 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a11004 ^ 1)
theorem ha11006 : a11006.IsHomogeneous 24 := by
  unfold a11006
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11000.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha11004.pow 1)))

@[irreducible]
def a11007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a01356 ^ 1)
theorem ha11007 : a11007.IsHomogeneous 36 := by
  unfold a11007
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1)))

end CycleQ2Concrete
