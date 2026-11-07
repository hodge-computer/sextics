import Proposal.CurrentAtoms038

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a11776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11773 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a11775 ^ 1)
theorem ha11776 : a11776.IsHomogeneous 6 := by
  unfold a11776
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha11775.pow 1)))

@[irreducible]
def a11777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11774 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11776 ^ 1)
theorem ha11777 : a11777.IsHomogeneous 6 := by
  unfold a11777
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11774.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11776.pow 1)))

@[irreducible]
def a11778 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a11777 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11369 ^ 1)
theorem ha11778 : a11778.IsHomogeneous 6 := by
  unfold a11778
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha11777.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11369.pow 1)))

@[irreducible]
def a11779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a11778 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a06426 ^ 1)
theorem ha11779 : a11779.IsHomogeneous 18 := by
  unfold a11779
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha11778.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha06426.pow 1)))

@[irreducible]
def a11780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11739 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11779 ^ 1) + (C ((45 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11754 ^ 1)
theorem ha11780 : a11780.IsHomogeneous 24 := by
  unfold a11780
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11739.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11779.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11754.pow 1)))

@[irreducible]
def a11781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11740 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11780 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11755 ^ 1)
theorem ha11781 : a11781.IsHomogeneous 30 := by
  unfold a11781
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11740.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11780.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11755.pow 1)))

@[irreducible]
def a11782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11741 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11756 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11781 ^ 1)
theorem ha11782 : a11782.IsHomogeneous 30 := by
  unfold a11782
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11741.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11756.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11781.pow 1)))

@[irreducible]
def a11783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11757 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11782 ^ 1)
theorem ha11783 : a11783.IsHomogeneous 30 := by
  unfold a11783
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11742.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11757.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11782.pow 1)))

@[irreducible]
def a11784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11747 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11783 ^ 1)
theorem ha11784 : a11784.IsHomogeneous 30 := by
  unfold a11784
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11762.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11783.pow 1)))

@[irreducible]
def a11785 : Poly := (C ((-7 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a11784 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a11221 ^ 1)
theorem ha11785 : a11785.IsHomogeneous 43 := by
  unfold a11785
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha11784.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha11221.pow 1)))

@[irreducible]
def a11786 : Poly := (C ((-14 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a11784 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11785 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a11221 ^ 1)
theorem ha11786 : a11786.IsHomogeneous 43 := by
  unfold a11786
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha11784.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha11221.pow 1)))

@[irreducible]
def a11787 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a11712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11567 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a11786 ^ 1)
theorem ha11787 : a11787.IsHomogeneous 54 := by
  unfold a11787
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha11712.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11567.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha11786.pow 1)))

@[irreducible]
def a11788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a03191 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00865 ^ 1 * a01473 ^ 1)
theorem ha11788 : a11788.IsHomogeneous 45 := by
  unfold a11788
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00865.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a11789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00577 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01473 ^ 1)
theorem ha11789 : a11789.IsHomogeneous 45 := by
  unfold a11789
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00577.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a11790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11788 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11789 ^ 1)
theorem ha11790 : a11790.IsHomogeneous 45 := by
  unfold a11790
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11788.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11789.pow 1)))

@[irreducible]
def a11791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a06158 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a03191 ^ 1)
theorem ha11791 : a11791.IsHomogeneous 39 := by
  unfold a11791
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha06158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a11792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11791 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a11788 ^ 1)
theorem ha11792 : a11792.IsHomogeneous 45 := by
  unfold a11792
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11791.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha11788.pow 1)))

@[irreducible]
def a11793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11790 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a11792 ^ 1)
theorem ha11793 : a11793.IsHomogeneous 45 := by
  unfold a11793
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11790.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha11792.pow 1)))

@[irreducible]
def a11794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00577 ^ 1 * a02008 ^ 1)
theorem ha11794 : a11794.IsHomogeneous 42 := by
  unfold a11794
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00577.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11794 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11789 ^ 1)
theorem ha11795 : a11795.IsHomogeneous 45 := by
  unfold a11795
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11794.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11789.pow 1)))

@[irreducible]
def a11796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11790 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11795 ^ 1)
theorem ha11796 : a11796.IsHomogeneous 45 := by
  unfold a11796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11790.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11795.pow 1)))

@[irreducible]
def a11797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11796 ^ 1)
theorem ha11797 : a11797.IsHomogeneous 45 := by
  unfold a11797
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11796.pow 1)))

@[irreducible]
def a11798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a07558 ^ 1)
theorem ha11798 : a11798.IsHomogeneous 36 := by
  unfold a11798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha07558.pow 1)))

@[irreducible]
def a11799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11794 ^ 1)
theorem ha11799 : a11799.IsHomogeneous 42 := by
  unfold a11799
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11798.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11794.pow 1)))

@[irreducible]
def a11800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11795 ^ 1)
theorem ha11800 : a11800.IsHomogeneous 45 := by
  unfold a11800
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11795.pow 1)))

@[irreducible]
def a11801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11796 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a11800 ^ 1)
theorem ha11801 : a11801.IsHomogeneous 45 := by
  unfold a11801
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11796.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha11800.pow 1)))

@[irreducible]
def a11802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11797 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11801 ^ 1)
theorem ha11802 : a11802.IsHomogeneous 45 := by
  unfold a11802
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11801.pow 1)))

@[irreducible]
def a11803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a11376 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a06158 ^ 1)
theorem ha11803 : a11803.IsHomogeneous 42 := by
  unfold a11803
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha11376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha06158.pow 1)))

@[irreducible]
def a11804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11803 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11791 ^ 1)
theorem ha11804 : a11804.IsHomogeneous 42 := by
  unfold a11804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11803.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11791.pow 1)))

@[irreducible]
def a11805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11804 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11792 ^ 1)
theorem ha11805 : a11805.IsHomogeneous 45 := by
  unfold a11805
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11804.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11792.pow 1)))

@[irreducible]
def a11806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11793 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a11805 ^ 1)
theorem ha11806 : a11806.IsHomogeneous 45 := by
  unfold a11806
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha11805.pow 1)))

@[irreducible]
def a11807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11797 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11806 ^ 1)
theorem ha11807 : a11807.IsHomogeneous 45 := by
  unfold a11807
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11806.pow 1)))

@[irreducible]
def a11808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11807 ^ 1)
theorem ha11808 : a11808.IsHomogeneous 45 := by
  unfold a11808
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11802.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11807.pow 1)))

@[irreducible]
def a11809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a11243 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11808 ^ 1)
theorem ha11809 : a11809.IsHomogeneous 50 := by
  unfold a11809
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha11243.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11808.pow 1)))

@[irreducible]
def a11810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11809 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11808 ^ 1)
theorem ha11810 : a11810.IsHomogeneous 50 := by
  unfold a11810
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11808.pow 1)))

@[irreducible]
def a11811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00655 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01327 ^ 1 * a01617 ^ 1)
theorem ha11811 : a11811.IsHomogeneous 39 := by
  unfold a11811
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00655.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01327.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a11812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01327 ^ 1 * a01617 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00506 ^ 1 * a03432 ^ 1)
theorem ha11812 : a11812.IsHomogeneous 45 := by
  unfold a11812
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00506.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a11813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11812 ^ 1)
theorem ha11813 : a11813.IsHomogeneous 45 := by
  unfold a11813
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11811.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11812.pow 1)))

@[irreducible]
def a11814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a02935 ^ 1)
theorem ha11814 : a11814.IsHomogeneous 42 := by
  unfold a11814
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11814 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11811 ^ 1)
theorem ha11815 : a11815.IsHomogeneous 42 := by
  unfold a11815
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11814.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11811.pow 1)))

@[irreducible]
def a11816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11815 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11813 ^ 1)
theorem ha11816 : a11816.IsHomogeneous 45 := by
  unfold a11816
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11813.pow 1)))

@[irreducible]
def a11817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a06529 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a03432 ^ 1)
theorem ha11817 : a11817.IsHomogeneous 45 := by
  unfold a11817
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha06529.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a11818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11812 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11817 ^ 1)
theorem ha11818 : a11818.IsHomogeneous 45 := by
  unfold a11818
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11812.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11817.pow 1)))

@[irreducible]
def a11819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11813 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11818 ^ 1)
theorem ha11819 : a11819.IsHomogeneous 45 := by
  unfold a11819
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11813.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11818.pow 1)))

@[irreducible]
def a11820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11816 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11819 ^ 1)
theorem ha11820 : a11820.IsHomogeneous 45 := by
  unfold a11820
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11816.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11819.pow 1)))

@[irreducible]
def a11821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a10779 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a05754 ^ 1)
theorem ha11821 : a11821.IsHomogeneous 42 := by
  unfold a11821
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha10779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a11822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11814 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11821 ^ 1)
theorem ha11822 : a11822.IsHomogeneous 42 := by
  unfold a11822
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11814.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11821.pow 1)))

@[irreducible]
def a11823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11815 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11822 ^ 1)
theorem ha11823 : a11823.IsHomogeneous 42 := by
  unfold a11823
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11822.pow 1)))

@[irreducible]
def a11824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11816 ^ 1)
theorem ha11824 : a11824.IsHomogeneous 45 := by
  unfold a11824
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11823.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11816.pow 1)))

@[irreducible]
def a11825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11824 ^ 1)
theorem ha11825 : a11825.IsHomogeneous 45 := by
  unfold a11825
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11824.pow 1)))

@[irreducible]
def a11826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00317 ^ 1)
theorem ha11826 : a11826.IsHomogeneous 21 := by
  unfold a11826
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a11827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00317 ^ 1)
theorem ha11827 : a11827.IsHomogeneous 27 := by
  unfold a11827
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)))

@[irreducible]
def a11828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha11828 : a11828.IsHomogeneous 27 := by
  unfold a11828
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a11829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11827 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a11828 ^ 1) + (C ((63 : ℂ) / (20 : ℂ)) * a00003 ^ 6 * a11826 ^ 1)
theorem ha11829 : a11829.IsHomogeneous 27 := by
  unfold a11829
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha11828.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((63 : ℂ) / (20 : ℂ))).mul (ha00003.pow 6)).mul (ha11826.pow 1)))

@[irreducible]
def a11830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha11830 : a11830.IsHomogeneous 24 := by
  unfold a11830
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a11831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11830 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a11826 ^ 1)
theorem ha11831 : a11831.IsHomogeneous 24 := by
  unfold a11831
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11830.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha11826.pow 1)))

@[irreducible]
def a11832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1)
theorem ha11832 : a11832.IsHomogeneous 30 := by
  unfold a11832
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a11833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11832 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11828 ^ 1) + (C ((28 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a11830 ^ 1)
theorem ha11833 : a11833.IsHomogeneous 30 := by
  unfold a11833
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11832.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11828.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha11830.pow 1)))

@[irreducible]
def a11834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11833 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11829 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11831 ^ 1)
theorem ha11834 : a11834.IsHomogeneous 30 := by
  unfold a11834
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11829.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11831.pow 1)))

@[irreducible]
def a11835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00865 ^ 1)
theorem ha11835 : a11835.IsHomogeneous 21 := by
  unfold a11835
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00865.pow 1)))

@[irreducible]
def a11836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11826 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a11835 ^ 1)
theorem ha11836 : a11836.IsHomogeneous 21 := by
  unfold a11836
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11826.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha11835.pow 1)))

@[irreducible]
def a11837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00865 ^ 1)
theorem ha11837 : a11837.IsHomogeneous 27 := by
  unfold a11837
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00865.pow 1)))

@[irreducible]
def a11838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11837 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11835 ^ 1)
theorem ha11838 : a11838.IsHomogeneous 27 := by
  unfold a11838
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11837.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11835.pow 1)))

@[irreducible]
def a11839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11838 ^ 1) + (C ((63 : ℂ) / (10 : ℂ)) * a00003 ^ 6 * a11836 ^ 1)
theorem ha11839 : a11839.IsHomogeneous 27 := by
  unfold a11839
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11838.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((63 : ℂ) / (10 : ℂ))).mul (ha00003.pow 6)).mul (ha11836.pow 1)))

@[irreducible]
def a11840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11831 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a11836 ^ 1)
theorem ha11840 : a11840.IsHomogeneous 24 := by
  unfold a11840
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha11836.pow 1)))

@[irreducible]
def a11841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11834 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11839 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11840 ^ 1)
theorem ha11841 : a11841.IsHomogeneous 30 := by
  unfold a11841
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11834.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11839.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11840.pow 1)))

@[irreducible]
def a11842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00865 ^ 1)
theorem ha11842 : a11842.IsHomogeneous 27 := by
  unfold a11842
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a02008 ^ 1)
theorem ha11843 : a11843.IsHomogeneous 27 := by
  unfold a11843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11827 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11843 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11842 ^ 1)
theorem ha11844 : a11844.IsHomogeneous 27 := by
  unfold a11844
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11843.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11842.pow 1)))

@[irreducible]
def a11845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1)
theorem ha11845 : a11845.IsHomogeneous 27 := by
  unfold a11845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a11846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11828 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11845 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11842 ^ 1)
theorem ha11846 : a11846.IsHomogeneous 27 := by
  unfold a11846
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11845.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11842.pow 1)))

@[irreducible]
def a11847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11844 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a11846 ^ 1)
theorem ha11847 : a11847.IsHomogeneous 27 := by
  unfold a11847
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11844.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha11846.pow 1)))

@[irreducible]
def a11848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1)
theorem ha11848 : a11848.IsHomogeneous 30 := by
  unfold a11848
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11832 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a11848 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11845 ^ 1)
theorem ha11849 : a11849.IsHomogeneous 30 := by
  unfold a11849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11832.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha11848.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11845.pow 1)))

@[irreducible]
def a11850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11849 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11846 ^ 1)
theorem ha11850 : a11850.IsHomogeneous 30 := by
  unfold a11850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11849.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11846.pow 1)))

@[irreducible]
def a11851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11850 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11847 ^ 1)
theorem ha11851 : a11851.IsHomogeneous 30 := by
  unfold a11851
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11834.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11850.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11847.pow 1)))

@[irreducible]
def a11852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a04086 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a02008 ^ 1)
theorem ha11852 : a11852.IsHomogeneous 24 := by
  unfold a11852
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha04086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11837 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11843 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a11852 ^ 1)
theorem ha11853 : a11853.IsHomogeneous 27 := by
  unfold a11853
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11837.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11843.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha11852.pow 1)))

@[irreducible]
def a11854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11838 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11844 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11853 ^ 1)
theorem ha11854 : a11854.IsHomogeneous 27 := by
  unfold a11854
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11838.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11844.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11853.pow 1)))

@[irreducible]
def a11855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11854 ^ 1)
theorem ha11855 : a11855.IsHomogeneous 27 := by
  unfold a11855
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11847.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11854.pow 1)))

@[irreducible]
def a11856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11851 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11855 ^ 1)
theorem ha11856 : a11856.IsHomogeneous 30 := by
  unfold a11856
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11851.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11855.pow 1)))

@[irreducible]
def a11857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00317 ^ 1)
theorem ha11857 : a11857.IsHomogeneous 27 := by
  unfold a11857
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)))

@[irreducible]
def a11858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00865 ^ 1)
theorem ha11858 : a11858.IsHomogeneous 27 := by
  unfold a11858
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00865.pow 1)))

@[irreducible]
def a11859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11858 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11835 ^ 1)
theorem ha11859 : a11859.IsHomogeneous 27 := by
  unfold a11859
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11857.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11858.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11835.pow 1)))

@[irreducible]
def a11860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00317 ^ 1)
theorem ha11860 : a11860.IsHomogeneous 27 := by
  unfold a11860
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a11861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11857 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a11860 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00003 ^ 6 * a11826 ^ 1)
theorem ha11861 : a11861.IsHomogeneous 27 := by
  unfold a11861
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11857.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha11860.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00003.pow 6)).mul (ha11826.pow 1)))

@[irreducible]
def a11862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11859 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11861 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a11836 ^ 1)
theorem ha11862 : a11862.IsHomogeneous 27 := by
  unfold a11862
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11859.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11861.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha11836.pow 1)))

@[irreducible]
def a11863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a02008 ^ 1)
theorem ha11863 : a11863.IsHomogeneous 30 := by
  unfold a11863
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11863 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11837 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a11858 ^ 1)
theorem ha11864 : a11864.IsHomogeneous 30 := by
  unfold a11864
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11863.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11837.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha11858.pow 1)))

@[irreducible]
def a11865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11864 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11838 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a11859 ^ 1)
theorem ha11865 : a11865.IsHomogeneous 30 := by
  unfold a11865
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11838.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha11859.pow 1)))

@[irreducible]
def a11866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11865 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11839 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a11862 ^ 1)
theorem ha11866 : a11866.IsHomogeneous 30 := by
  unfold a11866
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11839.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha11862.pow 1)))

@[irreducible]
def a11867 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00129 ^ 1)
theorem ha11867 : a11867.IsHomogeneous 30 := by
  unfold a11867
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11867 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11830 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11860 ^ 1)
theorem ha11868 : a11868.IsHomogeneous 30 := by
  unfold a11868
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11867.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11830.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11860.pow 1)))

@[irreducible]
def a11869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11868 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11861 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11831 ^ 1)
theorem ha11869 : a11869.IsHomogeneous 30 := by
  unfold a11869
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11868.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11861.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11831.pow 1)))

@[irreducible]
def a11870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11869 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11862 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11840 ^ 1)
theorem ha11870 : a11870.IsHomogeneous 30 := by
  unfold a11870
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11869.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11862.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11840.pow 1)))

@[irreducible]
def a11871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11866 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11870 ^ 1)
theorem ha11871 : a11871.IsHomogeneous 30 := by
  unfold a11871
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11866.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11870.pow 1)))

@[irreducible]
def a11872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a07558 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a04086 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a04086 ^ 1)
theorem ha11872 : a11872.IsHomogeneous 30 := by
  unfold a11872
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha07558.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a11873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11863 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a11872 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11852 ^ 1)
theorem ha11873 : a11873.IsHomogeneous 30 := by
  unfold a11873
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11863.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha11872.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11852.pow 1)))

@[irreducible]
def a11874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11873 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11853 ^ 1)
theorem ha11874 : a11874.IsHomogeneous 30 := by
  unfold a11874
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11864.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11873.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11853.pow 1)))

@[irreducible]
def a11875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11874 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11854 ^ 1)
theorem ha11875 : a11875.IsHomogeneous 30 := by
  unfold a11875
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11865.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11874.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11854.pow 1)))

@[irreducible]
def a11876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11875 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11855 ^ 1)
theorem ha11876 : a11876.IsHomogeneous 30 := by
  unfold a11876
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11866.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11875.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11855.pow 1)))

@[irreducible]
def a11877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11871 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11876 ^ 1)
theorem ha11877 : a11877.IsHomogeneous 30 := by
  unfold a11877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11856.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11871.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11876.pow 1)))

@[irreducible]
def a11878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00649 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a01607 ^ 1)
theorem ha11878 : a11878.IsHomogeneous 12 := by
  unfold a11878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha01607.pow 1)))

@[irreducible]
def a11879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01607 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a03417 ^ 1)
theorem ha11879 : a11879.IsHomogeneous 12 := by
  unfold a11879
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha03417.pow 1)))

@[irreducible]
def a11880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11878 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11879 ^ 1)
theorem ha11880 : a11880.IsHomogeneous 12 := by
  unfold a11880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11879.pow 1)))

@[irreducible]
def a11881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00649 ^ 1)
theorem ha11881 : a11881.IsHomogeneous 12 := by
  unfold a11881
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a11882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11878 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a11881 ^ 1)
theorem ha11882 : a11882.IsHomogeneous 12 := by
  unfold a11882
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha11881.pow 1)))

@[irreducible]
def a11883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11882 ^ 1)
theorem ha11883 : a11883.IsHomogeneous 12 := by
  unfold a11883
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11882.pow 1)))

@[irreducible]
def a11884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00032 ^ 1)
theorem ha11884 : a11884.IsHomogeneous 6 := by
  unfold a11884
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)))

@[irreducible]
def a11885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a11884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11881 ^ 1)
theorem ha11885 : a11885.IsHomogeneous 12 := by
  unfold a11885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha11884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11881.pow 1)))

@[irreducible]
def a11886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11882 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a11885 ^ 1)
theorem ha11886 : a11886.IsHomogeneous 12 := by
  unfold a11886
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha11885.pow 1)))

@[irreducible]
def a11887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11886 ^ 1)
theorem ha11887 : a11887.IsHomogeneous 12 := by
  unfold a11887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11886.pow 1)))

@[irreducible]
def a11888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03417 ^ 1) + (C ((42 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06508 ^ 1)
theorem ha11888 : a11888.IsHomogeneous 12 := by
  unfold a11888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03417.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06508.pow 1)))

@[irreducible]
def a11889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11879 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11888 ^ 1)
theorem ha11889 : a11889.IsHomogeneous 12 := by
  unfold a11889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11888.pow 1)))

@[irreducible]
def a11890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11880 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11889 ^ 1)
theorem ha11890 : a11890.IsHomogeneous 12 := by
  unfold a11890
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11889.pow 1)))

@[irreducible]
def a11891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11890 ^ 1)
theorem ha11891 : a11891.IsHomogeneous 12 := by
  unfold a11891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11890.pow 1)))

@[irreducible]
def a11892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11891 ^ 1)
theorem ha11892 : a11892.IsHomogeneous 12 := by
  unfold a11892
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11891.pow 1)))

@[irreducible]
def a11893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03357 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a03358 ^ 1)
theorem ha11893 : a11893.IsHomogeneous 6 := by
  unfold a11893
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03357.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha03358.pow 1)))

@[irreducible]
def a11894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03359 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a11893 ^ 1)
theorem ha11894 : a11894.IsHomogeneous 6 := by
  unfold a11894
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha11893.pow 1)))

@[irreducible]
def a11895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11893 ^ 1) + (C ((1 : ℂ) / (21 : ℂ)) * a11894 ^ 1)
theorem ha11895 : a11895.IsHomogeneous 6 := by
  unfold a11895
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (21 : ℂ))).mul (ha11894.pow 1)))

@[irreducible]
def a11896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a11895 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06508 ^ 1)
theorem ha11896 : a11896.IsHomogeneous 12 := by
  unfold a11896
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha11895.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06508.pow 1)))

@[irreducible]
def a11897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11888 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a11896 ^ 1)
theorem ha11897 : a11897.IsHomogeneous 12 := by
  unfold a11897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha11896.pow 1)))

@[irreducible]
def a11898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11889 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11897 ^ 1)
theorem ha11898 : a11898.IsHomogeneous 12 := by
  unfold a11898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11897.pow 1)))

@[irreducible]
def a11899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11890 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11898 ^ 1)
theorem ha11899 : a11899.IsHomogeneous 12 := by
  unfold a11899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11898.pow 1)))

@[irreducible]
def a11900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11899 ^ 1)
theorem ha11900 : a11900.IsHomogeneous 12 := by
  unfold a11900
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11899.pow 1)))

@[irreducible]
def a11901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11892 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11900 ^ 1)
theorem ha11901 : a11901.IsHomogeneous 12 := by
  unfold a11901
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11900.pow 1)))

@[irreducible]
def a11902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01469 ^ 1)
theorem ha11902 : a11902.IsHomogeneous 12 := by
  unfold a11902
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01469.pow 1)))

@[irreducible]
def a11903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a03186 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01469 ^ 1)
theorem ha11903 : a11903.IsHomogeneous 12 := by
  unfold a11903
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01469.pow 1)))

@[irreducible]
def a11904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11902 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11903 ^ 1)
theorem ha11904 : a11904.IsHomogeneous 12 := by
  unfold a11904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11903.pow 1)))

@[irreducible]
def a11905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00574 ^ 1)
theorem ha11905 : a11905.IsHomogeneous 12 := by
  unfold a11905
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00574.pow 1)))

@[irreducible]
def a11906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11902 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a11905 ^ 1)
theorem ha11906 : a11906.IsHomogeneous 12 := by
  unfold a11906
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha11905.pow 1)))

@[irreducible]
def a11907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11906 ^ 1)
theorem ha11907 : a11907.IsHomogeneous 12 := by
  unfold a11907
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11906.pow 1)))

@[irreducible]
def a11908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a06152 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00324 ^ 1 * a03186 ^ 1)
theorem ha11908 : a11908.IsHomogeneous 12 := by
  unfold a11908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha06152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a11909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11903 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11908 ^ 1)
theorem ha11909 : a11909.IsHomogeneous 12 := by
  unfold a11909
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11908.pow 1)))

@[irreducible]
def a11910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11909 ^ 1)
theorem ha11910 : a11910.IsHomogeneous 12 := by
  unfold a11910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11909.pow 1)))

@[irreducible]
def a11911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11910 ^ 1)
theorem ha11911 : a11911.IsHomogeneous 12 := by
  unfold a11911
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11910.pow 1)))

@[irreducible]
def a11912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00025 ^ 1)
theorem ha11912 : a11912.IsHomogeneous 6 := by
  unfold a11912
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00025.pow 1)))

@[irreducible]
def a11913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a11912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11905 ^ 1)
theorem ha11913 : a11913.IsHomogeneous 12 := by
  unfold a11913
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha11912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11905.pow 1)))

@[irreducible]
def a11914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11906 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a11913 ^ 1)
theorem ha11914 : a11914.IsHomogeneous 12 := by
  unfold a11914
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha11913.pow 1)))

@[irreducible]
def a11915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11914 ^ 1)
theorem ha11915 : a11915.IsHomogeneous 12 := by
  unfold a11915
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11914.pow 1)))

@[irreducible]
def a11916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11915 ^ 1)
theorem ha11916 : a11916.IsHomogeneous 12 := by
  unfold a11916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11915.pow 1)))

@[irreducible]
def a11917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a11369 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a06152 ^ 1)
theorem ha11917 : a11917.IsHomogeneous 12 := by
  unfold a11917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha11369.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha06152.pow 1)))

@[irreducible]
def a11918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11908 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11917 ^ 1)
theorem ha11918 : a11918.IsHomogeneous 12 := by
  unfold a11918
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11917.pow 1)))

@[irreducible]
def a11919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11909 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11918 ^ 1)
theorem ha11919 : a11919.IsHomogeneous 12 := by
  unfold a11919
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11909.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11918.pow 1)))

@[irreducible]
def a11920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11910 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11919 ^ 1)
theorem ha11920 : a11920.IsHomogeneous 12 := by
  unfold a11920
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11910.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11919.pow 1)))

@[irreducible]
def a11921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11920 ^ 1)
theorem ha11921 : a11921.IsHomogeneous 12 := by
  unfold a11921
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11920.pow 1)))

@[irreducible]
def a11922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11921 ^ 1)
theorem ha11922 : a11922.IsHomogeneous 12 := by
  unfold a11922
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11916.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11921.pow 1)))

@[irreducible]
def a11923 : Poly := (C ((-7 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11877 ^ 1) + (C ((49 : ℂ) / (36 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11922 ^ 1)
theorem ha11923 : a11923.IsHomogeneous 30 := by
  unfold a11923
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11877.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((49 : ℂ) / (36 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11922.pow 1)))

@[irreducible]
def a11924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a06529 ^ 1)
theorem ha11924 : a11924.IsHomogeneous 36 := by
  unfold a11924
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha06529.pow 1)))

@[irreducible]
def a11925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11924 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11817 ^ 1)
theorem ha11925 : a11925.IsHomogeneous 45 := by
  unfold a11925
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11924.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11817.pow 1)))

@[irreducible]
def a11926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11818 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11925 ^ 1)
theorem ha11926 : a11926.IsHomogeneous 45 := by
  unfold a11926
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11818.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11925.pow 1)))

@[irreducible]
def a11927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11926 ^ 1)
theorem ha11927 : a11927.IsHomogeneous 45 := by
  unfold a11927
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11819.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11926.pow 1)))

@[irreducible]
def a11928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11820 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11927 ^ 1)
theorem ha11928 : a11928.IsHomogeneous 45 := by
  unfold a11928
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11927.pow 1)))

@[irreducible]
def a11929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11928 ^ 1)
theorem ha11929 : a11929.IsHomogeneous 45 := by
  unfold a11929
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11825.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11928.pow 1)))

@[irreducible]
def a11930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a11243 ^ 1) + (C ((4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11929 ^ 1)
theorem ha11930 : a11930.IsHomogeneous 50 := by
  unfold a11930
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha11243.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11929.pow 1)))

@[irreducible]
def a11931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11930 ^ 1)
theorem ha11931 : a11931.IsHomogeneous 50 := by
  unfold a11931
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11930.pow 1)))

@[irreducible]
def a11932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11810 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11931 ^ 1)
theorem ha11932 : a11932.IsHomogeneous 50 := by
  unfold a11932
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11810.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11931.pow 1)))

@[irreducible]
def a11933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11810 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11808 ^ 1)
theorem ha11933 : a11933.IsHomogeneous 50 := by
  unfold a11933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11810.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11808.pow 1)))

@[irreducible]
def a11934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11932 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11933 ^ 1)
theorem ha11934 : a11934.IsHomogeneous 50 := by
  unfold a11934
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11933.pow 1)))

@[irreducible]
def a11935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00547 ^ 1)
theorem ha11935 : a11935.IsHomogeneous 39 := by
  unfold a11935
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a00547 ^ 1)
theorem ha11936 : a11936.IsHomogeneous 39 := by
  unfold a11936
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00317 ^ 1)
theorem ha11937 : a11937.IsHomogeneous 39 := by
  unfold a11937
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a11938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11935 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a11937 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11936 ^ 1)
theorem ha11938 : a11938.IsHomogeneous 39 := by
  unfold a11938
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha11937.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11936.pow 1)))

@[irreducible]
def a11939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00317 ^ 1 * a01412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00547 ^ 1)
theorem ha11939 : a11939.IsHomogeneous 45 := by
  unfold a11939
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01412 ^ 1)
theorem ha11940 : a11940.IsHomogeneous 39 := by
  unfold a11940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11935 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11940 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a11939 ^ 1)
theorem ha11941 : a11941.IsHomogeneous 45 := by
  unfold a11941
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11940.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha11939.pow 1)))

@[irreducible]
def a11942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a00865 ^ 1)
theorem ha11942 : a11942.IsHomogeneous 45 := by
  unfold a11942
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11936 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11939 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a11942 ^ 1)
theorem ha11943 : a11943.IsHomogeneous 45 := by
  unfold a11943
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11939.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha11942.pow 1)))

@[irreducible]
def a11944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11941 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11943 ^ 1)
theorem ha11944 : a11944.IsHomogeneous 45 := by
  unfold a11944
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11941.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11943.pow 1)))

@[irreducible]
def a11945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00547 ^ 1)
theorem ha11945 : a11945.IsHomogeneous 42 := by
  unfold a11945
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a03085 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01412 ^ 1)
theorem ha11946 : a11946.IsHomogeneous 36 := by
  unfold a11946
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11945 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11946 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11935 ^ 1)
theorem ha11947 : a11947.IsHomogeneous 42 := by
  unfold a11947
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11946.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11935.pow 1)))

@[irreducible]
def a11948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00547 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1)
theorem ha11948 : a11948.IsHomogeneous 42 := by
  unfold a11948
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a11949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11945 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11948 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11937 ^ 1)
theorem ha11949 : a11949.IsHomogeneous 42 := by
  unfold a11949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11945.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11948.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11937.pow 1)))

@[irreducible]
def a11950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11949 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11938 ^ 1)
theorem ha11950 : a11950.IsHomogeneous 42 := by
  unfold a11950
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11949.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11938.pow 1)))

@[irreducible]
def a11951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a05994 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a03085 ^ 1)
theorem ha11951 : a11951.IsHomogeneous 42 := by
  unfold a11951
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11951 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11940 ^ 1) + (C ((35 : ℂ) / (48 : ℂ)) * a00003 ^ 6 * a11946 ^ 1)
theorem ha11952 : a11952.IsHomogeneous 42 := by
  unfold a11952
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11951.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11940.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (48 : ℂ))).mul (ha00003.pow 6)).mul (ha11946.pow 1)))

@[irreducible]
def a11953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11947 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11941 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a11952 ^ 1)
theorem ha11953 : a11953.IsHomogeneous 45 := by
  unfold a11953
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11941.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha11952.pow 1)))

@[irreducible]
def a11954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11953 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11944 ^ 1)
theorem ha11954 : a11954.IsHomogeneous 45 := by
  unfold a11954
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11953.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11944.pow 1)))

@[irreducible]
def a11955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00865 ^ 1)
theorem ha11955 : a11955.IsHomogeneous 33 := by
  unfold a11955
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a02008 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00865 ^ 1)
theorem ha11956 : a11956.IsHomogeneous 33 := by
  unfold a11956
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a11957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11955 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11936 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a11956 ^ 1)
theorem ha11957 : a11957.IsHomogeneous 39 := by
  unfold a11957
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11936.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha11956.pow 1)))

@[irreducible]
def a11958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1)
theorem ha11958 : a11958.IsHomogeneous 33 := by
  unfold a11958
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a11959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11955 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a11958 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a11937 ^ 1)
theorem ha11959 : a11959.IsHomogeneous 39 := by
  unfold a11959
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11955.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha11958.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha11937.pow 1)))

@[irreducible]
def a11960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11938 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11957 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11959 ^ 1)
theorem ha11960 : a11960.IsHomogeneous 39 := by
  unfold a11960
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11957.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11959.pow 1)))

@[irreducible]
def a11961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a02008 ^ 1)
theorem ha11961 : a11961.IsHomogeneous 36 := by
  unfold a11961
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11961 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11942 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11956 ^ 1)
theorem ha11962 : a11962.IsHomogeneous 45 := by
  unfold a11962
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11961.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11942.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11956.pow 1)))

@[irreducible]
def a11963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11943 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a11962 ^ 1)
theorem ha11963 : a11963.IsHomogeneous 45 := by
  unfold a11963
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11943.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha11962.pow 1)))

@[irreducible]
def a11964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11944 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11963 ^ 1)
theorem ha11964 : a11964.IsHomogeneous 45 := by
  unfold a11964
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11944.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11963.pow 1)))

@[irreducible]
def a11965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00168 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha11965 : a11965.IsHomogeneous 36 := by
  unfold a11965
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00168.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a11966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11948 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a11958 ^ 1)
theorem ha11966 : a11966.IsHomogeneous 42 := by
  unfold a11966
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11965.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11948.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha11958.pow 1)))

@[irreducible]
def a11967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11949 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11966 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a11959 ^ 1)
theorem ha11967 : a11967.IsHomogeneous 42 := by
  unfold a11967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11966.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha11959.pow 1)))

@[irreducible]
def a11968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11967 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11960 ^ 1)
theorem ha11968 : a11968.IsHomogeneous 42 := by
  unfold a11968
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11967.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11960.pow 1)))

@[irreducible]
def a11969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11968 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11954 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11964 ^ 1)
theorem ha11969 : a11969.IsHomogeneous 45 := by
  unfold a11969
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11968.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11954.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11964.pow 1)))

@[irreducible]
def a11970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a03085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00865 ^ 1 * a01412 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a01412 ^ 1)
theorem ha11970 : a11970.IsHomogeneous 39 := by
  unfold a11970
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00547 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00865 ^ 1 * a01412 ^ 1)
theorem ha11971 : a11971.IsHomogeneous 45 := by
  unfold a11971
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00865.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11970 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11939 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a11971 ^ 1)
theorem ha11972 : a11972.IsHomogeneous 45 := by
  unfold a11972
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11939.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha11971.pow 1)))

@[irreducible]
def a11973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a05994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a03085 ^ 1)
theorem ha11973 : a11973.IsHomogeneous 39 := by
  unfold a11973
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha05994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11973 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11970 ^ 1)
theorem ha11974 : a11974.IsHomogeneous 39 := by
  unfold a11974
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11973.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11970.pow 1)))

@[irreducible]
def a11975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11974 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11972 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a11941 ^ 1)
theorem ha11975 : a11975.IsHomogeneous 45 := by
  unfold a11975
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11974.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11972.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha11941.pow 1)))

@[irreducible]
def a11976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02008 ^ 1)
theorem ha11976 : a11976.IsHomogeneous 42 := by
  unfold a11976
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a11977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11976 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11971 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11942 ^ 1)
theorem ha11977 : a11977.IsHomogeneous 45 := by
  unfold a11977
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11971.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11942.pow 1)))

@[irreducible]
def a11978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11943 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11972 ^ 1) + (C ((2 : ℂ) / (35 : ℂ)) * a11977 ^ 1)
theorem ha11978 : a11978.IsHomogeneous 45 := by
  unfold a11978
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11972.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (35 : ℂ))).mul (ha11977.pow 1)))

@[irreducible]
def a11979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11944 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a11975 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11978 ^ 1)
theorem ha11979 : a11979.IsHomogeneous 45 := by
  unfold a11979
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11944.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha11975.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11978.pow 1)))

@[irreducible]
def a11980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a11138 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a05994 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a05994 ^ 1)
theorem ha11980 : a11980.IsHomogeneous 42 := by
  unfold a11980
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha11138.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha05994.pow 1)))

@[irreducible]
def a11981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11951 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11980 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11973 ^ 1)
theorem ha11981 : a11981.IsHomogeneous 42 := by
  unfold a11981
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11951.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11980.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11973.pow 1)))

@[irreducible]
def a11982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11952 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11981 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11974 ^ 1)
theorem ha11982 : a11982.IsHomogeneous 42 := by
  unfold a11982
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11952.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11981.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11974.pow 1)))

@[irreducible]
def a11983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11982 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11975 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a11953 ^ 1)
theorem ha11983 : a11983.IsHomogeneous 45 := by
  unfold a11983
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11975.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha11953.pow 1)))

@[irreducible]
def a11984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11954 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11979 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a11983 ^ 1)
theorem ha11984 : a11984.IsHomogeneous 45 := by
  unfold a11984
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11954.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11979.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha11983.pow 1)))

@[irreducible]
def a11985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a04086 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a07558 ^ 1)
theorem ha11985 : a11985.IsHomogeneous 36 := by
  unfold a11985
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha04086.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha04086.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha07558.pow 1)))

@[irreducible]
def a11986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11961 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11985 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11976 ^ 1)
theorem ha11986 : a11986.IsHomogeneous 42 := by
  unfold a11986
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11961.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11985.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11976.pow 1)))

@[irreducible]
def a11987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11986 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11962 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11977 ^ 1)
theorem ha11987 : a11987.IsHomogeneous 45 := by
  unfold a11987
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11986.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11977.pow 1)))

@[irreducible]
def a11988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11978 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a11987 ^ 1)
theorem ha11988 : a11988.IsHomogeneous 45 := by
  unfold a11988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11963.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11978.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha11987.pow 1)))

@[irreducible]
def a11989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11964 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11979 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11988 ^ 1)
theorem ha11989 : a11989.IsHomogeneous 45 := by
  unfold a11989
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11964.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11979.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11988.pow 1)))

@[irreducible]
def a11990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11969 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11984 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11989 ^ 1)
theorem ha11990 : a11990.IsHomogeneous 45 := by
  unfold a11990
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11969.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11984.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11989.pow 1)))

@[irreducible]
def a11991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a10903 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11990 ^ 1)
theorem ha11991 : a11991.IsHomogeneous 50 := by
  unfold a11991
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha10903.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11990.pow 1)))

@[irreducible]
def a11992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11991 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a11990 ^ 1)
theorem ha11992 : a11992.IsHomogeneous 50 := by
  unfold a11992
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11991.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha11990.pow 1)))

@[irreducible]
def a11993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a01327 ^ 1)
theorem ha11993 : a11993.IsHomogeneous 39 := by
  unfold a11993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00621 ^ 1 * a01327 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00506 ^ 1 * a00621 ^ 1)
theorem ha11994 : a11994.IsHomogeneous 45 := by
  unfold a11994
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00506.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a11995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a01327 ^ 1)
theorem ha11995 : a11995.IsHomogeneous 39 := by
  unfold a11995
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11993 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a11995 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11994 ^ 1)
theorem ha11996 : a11996.IsHomogeneous 45 := by
  unfold a11996
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11993.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha11995.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11994.pow 1)))

@[irreducible]
def a11997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00621 ^ 1)
theorem ha11997 : a11997.IsHomogeneous 39 := by
  unfold a11997
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a11998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00621 ^ 1)
theorem ha11998 : a11998.IsHomogeneous 39 := by
  unfold a11998
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a11999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11993 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11998 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11997 ^ 1)
theorem ha11999 : a11999.IsHomogeneous 39 := by
  unfold a11999
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11998.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11997.pow 1)))

@[irreducible]
def a12000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a03330 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a01555 ^ 1)
theorem ha12000 : a12000.IsHomogeneous 45 := by
  unfold a12000
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a12001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11997 ^ 1) + (C ((4 : ℂ) / (35 : ℂ)) * a12000 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a11994 ^ 1)
theorem ha12001 : a12001.IsHomogeneous 45 := by
  unfold a12001
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11997.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (35 : ℂ))).mul (ha12000.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha11994.pow 1)))

@[irreducible]
def a12002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11999 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11996 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12001 ^ 1)
theorem ha12002 : a12002.IsHomogeneous 45 := by
  unfold a12002
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11996.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12001.pow 1)))

@[irreducible]
def a12003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a01327 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00506 ^ 1)
theorem ha12003 : a12003.IsHomogeneous 42 := by
  unfold a12003
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a12004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a01327 ^ 1)
theorem ha12004 : a12004.IsHomogeneous 36 := by
  unfold a12004
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a12005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12003 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a12004 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11993 ^ 1)
theorem ha12005 : a12005.IsHomogeneous 42 := by
  unfold a12005
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12003.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha12004.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11993.pow 1)))

@[irreducible]
def a12006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a02935 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a02935 ^ 1)
theorem ha12006 : a12006.IsHomogeneous 42 := by
  unfold a12006
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a12007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12006 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a12004 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11995 ^ 1)
theorem ha12007 : a12007.IsHomogeneous 42 := by
  unfold a12007
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha12004.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11995.pow 1)))

@[irreducible]
def a12008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12005 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a12007 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a11996 ^ 1)
theorem ha12008 : a12008.IsHomogeneous 45 := by
  unfold a12008
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12005.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha12007.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha11996.pow 1)))

@[irreducible]
def a12009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00506 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1)
theorem ha12009 : a12009.IsHomogeneous 42 := by
  unfold a12009
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a12010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12003 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12009 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11998 ^ 1)
theorem ha12010 : a12010.IsHomogeneous 42 := by
  unfold a12010
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11998.pow 1)))

@[irreducible]
def a12011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12010 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a11999 ^ 1)
theorem ha12011 : a12011.IsHomogeneous 42 := by
  unfold a12011
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12010.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha11999.pow 1)))

@[irreducible]
def a12012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12011 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12008 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12002 ^ 1)
theorem ha12012 : a12012.IsHomogeneous 45 := by
  unfold a12012
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12011.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12008.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12002.pow 1)))

@[irreducible]
def a12013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01555 ^ 1)
theorem ha12013 : a12013.IsHomogeneous 33 := by
  unfold a12013
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a12014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03330 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01555 ^ 1)
theorem ha12014 : a12014.IsHomogeneous 33 := by
  unfold a12014
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03330.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a12015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11997 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a12014 ^ 1)
theorem ha12015 : a12015.IsHomogeneous 39 := by
  unfold a12015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11997.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha12014.pow 1)))

@[irreducible]
def a12016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00201 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00621 ^ 1)
theorem ha12016 : a12016.IsHomogeneous 33 := by
  unfold a12016
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a12017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12013 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12016 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a11998 ^ 1)
theorem ha12017 : a12017.IsHomogeneous 39 := by
  unfold a12017
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12013.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12016.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha11998.pow 1)))

@[irreducible]
def a12018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11999 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12015 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12017 ^ 1)
theorem ha12018 : a12018.IsHomogeneous 39 := by
  unfold a12018
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12015.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12017.pow 1)))

@[irreducible]
def a12019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a03330 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03330 ^ 1)
theorem ha12019 : a12019.IsHomogeneous 36 := by
  unfold a12019
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a12020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12000 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a12014 ^ 1)
theorem ha12020 : a12020.IsHomogeneous 45 := by
  unfold a12020
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12000.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha12014.pow 1)))

@[irreducible]
def a12021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12015 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12001 ^ 1) + (C ((4 : ℂ) / (35 : ℂ)) * a12020 ^ 1)
theorem ha12021 : a12021.IsHomogeneous 45 := by
  unfold a12021
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12015.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12001.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (35 : ℂ))).mul (ha12020.pow 1)))

@[irreducible]
def a12022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12018 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12002 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12021 ^ 1)
theorem ha12022 : a12022.IsHomogeneous 45 := by
  unfold a12022
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12002.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12021.pow 1)))

@[irreducible]
def a12023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha12023 : a12023.IsHomogeneous 36 := by
  unfold a12023
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a12024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12009 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12016 ^ 1)
theorem ha12024 : a12024.IsHomogeneous 42 := by
  unfold a12024
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12009.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12016.pow 1)))

@[irreducible]
def a12025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12010 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12024 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a12017 ^ 1)
theorem ha12025 : a12025.IsHomogeneous 42 := by
  unfold a12025
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12010.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12024.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha12017.pow 1)))

@[irreducible]
def a12026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12011 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12025 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12018 ^ 1)
theorem ha12026 : a12026.IsHomogeneous 42 := by
  unfold a12026
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12011.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12018.pow 1)))

@[irreducible]
def a12027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12012 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12022 ^ 1)
theorem ha12027 : a12027.IsHomogeneous 45 := by
  unfold a12027
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12012.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12022.pow 1)))

@[irreducible]
def a12028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00025 ^ 1 * a01327 ^ 1 * a01555 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a01327 ^ 1)
theorem ha12028 : a12028.IsHomogeneous 39 := by
  unfold a12028
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a12029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00506 ^ 1 * a03330 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1 * a01555 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01555 ^ 1)
theorem ha12029 : a12029.IsHomogeneous 45 := by
  unfold a12029
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha03330.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a12030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12028 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12029 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a11994 ^ 1)
theorem ha12030 : a12030.IsHomogeneous 45 := by
  unfold a12030
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12029.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha11994.pow 1)))

@[irreducible]
def a12031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a02935 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a02935 ^ 1)
theorem ha12031 : a12031.IsHomogeneous 39 := by
  unfold a12031
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha02935.pow 1)))

end CycleQ2Concrete
