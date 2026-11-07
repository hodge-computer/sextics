import Proposal.CurrentAtoms042

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a12800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (30 : ℂ)) * a00014 ^ 1)
theorem ha12800 : a12800.IsHomogeneous 6 := by
  unfold a12800
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (30 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a12801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12795 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12800 ^ 1)
theorem ha12801 : a12801.IsHomogeneous 12 := by
  unfold a12801
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12795.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12800.pow 1)))

@[irreducible]
def a12802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12796 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12801 ^ 1)
theorem ha12802 : a12802.IsHomogeneous 18 := by
  unfold a12802
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12796.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12801.pow 1)))

@[irreducible]
def a12803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12799 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12802 ^ 1)
theorem ha12803 : a12803.IsHomogeneous 24 := by
  unfold a12803
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12799.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12802.pow 1)))

@[irreducible]
def a12804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00518 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha12804 : a12804.IsHomogeneous 6 := by
  unfold a12804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a12805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha12805 : a12805.IsHomogeneous 6 := by
  unfold a12805
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a12806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12805 ^ 1) + (C ((20 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12804 ^ 1)
theorem ha12806 : a12806.IsHomogeneous 12 := by
  unfold a12806
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12805.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12804.pow 1)))

@[irreducible]
def a12807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01353 ^ 1)
theorem ha12807 : a12807.IsHomogeneous 12 := by
  unfold a12807
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01353.pow 1)))

@[irreducible]
def a12808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12807 ^ 1)
theorem ha12808 : a12808.IsHomogeneous 12 := by
  unfold a12808
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12804.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12807.pow 1)))

@[irreducible]
def a12809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12806 ^ 1) + (C ((20 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12808 ^ 1)
theorem ha12809 : a12809.IsHomogeneous 18 := by
  unfold a12809
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12806.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12808.pow 1)))

@[irreducible]
def a12810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01353 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a02981 ^ 1)
theorem ha12810 : a12810.IsHomogeneous 18 := by
  unfold a12810
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha02981.pow 1)))

@[irreducible]
def a12811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12807 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12810 ^ 1)
theorem ha12811 : a12811.IsHomogeneous 18 := by
  unfold a12811
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12807.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12810.pow 1)))

@[irreducible]
def a12812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12808 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12811 ^ 1)
theorem ha12812 : a12812.IsHomogeneous 18 := by
  unfold a12812
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12808.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12811.pow 1)))

@[irreducible]
def a12813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12809 ^ 1) + (C ((20 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12812 ^ 1)
theorem ha12813 : a12813.IsHomogeneous 24 := by
  unfold a12813
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12812.pow 1)))

@[irreducible]
def a12814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07116 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a12813 ^ 1)
theorem ha12814 : a12814.IsHomogeneous 24 := by
  unfold a12814
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha12813.pow 1)))

@[irreducible]
def a12815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12797 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12814 ^ 1)
theorem ha12815 : a12815.IsHomogeneous 24 := by
  unfold a12815
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12797.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12814.pow 1)))

@[irreducible]
def a12816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12815 ^ 1)
theorem ha12816 : a12816.IsHomogeneous 24 := by
  unfold a12816
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12798.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12815.pow 1)))

@[irreducible]
def a12817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12816 ^ 1)
theorem ha12817 : a12817.IsHomogeneous 24 := by
  unfold a12817
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12799.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12816.pow 1)))

@[irreducible]
def a12818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12803 ^ 1)
theorem ha12818 : a12818.IsHomogeneous 30 := by
  unfold a12818
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12803.pow 1)))

@[irreducible]
def a12819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a07120 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00289 ^ 1 * a07120 ^ 1) + (C ((25 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12818 ^ 1)
theorem ha12819 : a12819.IsHomogeneous 145 := by
  unfold a12819
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha07120.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha07120.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12818.pow 1)))

@[irreducible]
def a12820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12787 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12819 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a12777 ^ 1)
theorem ha12820 : a12820.IsHomogeneous 200 := by
  unfold a12820
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12787.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12819.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12777.pow 1)))

@[irreducible]
def a12821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12788 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12820 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12778 ^ 1)
theorem ha12821 : a12821.IsHomogeneous 200 := by
  unfold a12821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12788.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12820.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12778.pow 1)))

@[irreducible]
def a12822 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12821 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12779 ^ 1)
theorem ha12822 : a12822.IsHomogeneous 200 := by
  unfold a12822
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12821.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12779.pow 1)))

@[irreducible]
def a12823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12822 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12783 ^ 1)
theorem ha12823 : a12823.IsHomogeneous 200 := by
  unfold a12823
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12822.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12783.pow 1)))

@[irreducible]
def a12824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00785 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00785 ^ 1 * a03812 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01848 ^ 1 * a01852 ^ 1)
theorem ha12824 : a12824.IsHomogeneous 172 := by
  unfold a12824
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00785.pow 1)).mul (ha01848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha03812.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01848.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00783 ^ 1 * a01852 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a01848 ^ 1 * a01852 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a03819 ^ 1)
theorem ha12825 : a12825.IsHomogeneous 172 := by
  unfold a12825
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00783.pow 1)).mul (ha01852.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha01848.pow 1)).mul (ha01852.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12768 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12824 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12825 ^ 1)
theorem ha12826 : a12826.IsHomogeneous 178 := by
  unfold a12826
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12824.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12825.pow 1)))

@[irreducible]
def a12827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a07133 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00785 ^ 1 * a03812 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00265 ^ 1 * a03812 ^ 1)
theorem ha12827 : a12827.IsHomogeneous 172 := by
  unfold a12827
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha07133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha03812.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha03812.pow 1)))

@[irreducible]
def a12828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12769 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12824 ^ 1) + (C ((1 : ℂ) / (30 : ℂ)) * a00014 ^ 1 * a12827 ^ 1)
theorem ha12828 : a12828.IsHomogeneous 178 := by
  unfold a12828
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12769.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12824.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (30 : ℂ))).mul (ha00014.pow 1)).mul (ha12827.pow 1)))

@[irreducible]
def a12829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12828 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12826 ^ 1)
theorem ha12829 : a12829.IsHomogeneous 184 := by
  unfold a12829
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12770.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12828.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12826.pow 1)))

@[irreducible]
def a12830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a07143 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a03819 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00289 ^ 1 * a03819 ^ 1)
theorem ha12830 : a12830.IsHomogeneous 172 := by
  unfold a12830
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha07143.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha03819.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00289.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12825 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a12830 ^ 1)
theorem ha12831 : a12831.IsHomogeneous 178 := by
  unfold a12831
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12771.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12825.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha12830.pow 1)))

@[irreducible]
def a12832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12772 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12826 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12831 ^ 1)
theorem ha12832 : a12832.IsHomogeneous 184 := by
  unfold a12832
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12826.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12831.pow 1)))

@[irreducible]
def a12833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12773 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12832 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12829 ^ 1)
theorem ha12833 : a12833.IsHomogeneous 190 := by
  unfold a12833
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12773.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12832.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12829.pow 1)))

@[irreducible]
def a12834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((4 : ℂ) / (9 : ℂ)) * a01845 ^ 1)
theorem ha12834 : a12834.IsHomogeneous 6 := by
  unfold a12834
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha01845.pow 1)))

@[irreducible]
def a12835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (2 : ℂ)) * a12834 ^ 1)
theorem ha12835 : a12835.IsHomogeneous 6 := by
  unfold a12835
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12834.pow 1)))

@[irreducible]
def a12836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 2 * a12835 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a00012 ^ 6) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1)
theorem ha12836 : a12836.IsHomogeneous 54 := by
  unfold a12836
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 2)).mul (ha12835.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 6))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1)))

@[irreducible]
def a12837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a07133 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a07133 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a12836 ^ 1)
theorem ha12837 : a12837.IsHomogeneous 115 := by
  unfold a12837
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha07133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha07133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12836.pow 1)))

@[irreducible]
def a12838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a12837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12827 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a12780 ^ 1)
theorem ha12838 : a12838.IsHomogeneous 178 := by
  unfold a12838
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12827.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha12780.pow 1)))

@[irreducible]
def a12839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12781 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12838 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12828 ^ 1)
theorem ha12839 : a12839.IsHomogeneous 184 := by
  unfold a12839
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12838.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12828.pow 1)))

@[irreducible]
def a12840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12782 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a12839 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12829 ^ 1)
theorem ha12840 : a12840.IsHomogeneous 190 := by
  unfold a12840
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12782.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha12839.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12829.pow 1)))

@[irreducible]
def a12841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12783 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12840 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12833 ^ 1)
theorem ha12841 : a12841.IsHomogeneous 196 := by
  unfold a12841
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12783.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12840.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12833.pow 1)))

@[irreducible]
def a12842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00723 ^ 1 * a03601 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a01724 ^ 2)
theorem ha12842 : a12842.IsHomogeneous 106 := by
  unfold a12842
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00723.pow 1)).mul (ha03601.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha01724.pow 2)))

@[irreducible]
def a12843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00265 ^ 1 * a06786 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00723 ^ 1 * a03601 ^ 1)
theorem ha12843 : a12843.IsHomogeneous 106 := by
  unfold a12843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00265.pow 1)).mul (ha06786.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00723.pow 1)).mul (ha03601.pow 1)))

@[irreducible]
def a12844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12842 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a12843 ^ 1)
theorem ha12844 : a12844.IsHomogeneous 106 := by
  unfold a12844
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha12843.pow 1)))

@[irreducible]
def a12845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12842 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12844 ^ 1)
theorem ha12845 : a12845.IsHomogeneous 106 := by
  unfold a12845
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12844.pow 1)))

@[irreducible]
def a12846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12299 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a06786 ^ 1)
theorem ha12846 : a12846.IsHomogeneous 104 := by
  unfold a12846
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha06786.pow 1)))

@[irreducible]
def a12847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12846 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a12843 ^ 1)
theorem ha12847 : a12847.IsHomogeneous 106 := by
  unfold a12847
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha12843.pow 1)))

@[irreducible]
def a12848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12844 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12847 ^ 1)
theorem ha12848 : a12848.IsHomogeneous 106 := by
  unfold a12848
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12844.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12847.pow 1)))

@[irreducible]
def a12849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12845 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12848 ^ 1)
theorem ha12849 : a12849.IsHomogeneous 106 := by
  unfold a12849
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12845.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12848.pow 1)))

@[irreducible]
def a12850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12845 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12849 ^ 1)
theorem ha12850 : a12850.IsHomogeneous 106 := by
  unfold a12850
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12845.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12849.pow 1)))

@[irreducible]
def a12851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a07143 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00124 ^ 1 * a07143 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a12850 ^ 1)
theorem ha12851 : a12851.IsHomogeneous 172 := by
  unfold a12851
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha07143.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00124.pow 1)).mul (ha07143.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha12850.pow 1)))

@[irreducible]
def a12852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12790 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a12830 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a12851 ^ 1)
theorem ha12852 : a12852.IsHomogeneous 178 := by
  unfold a12852
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12790.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha12830.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha12851.pow 1)))

@[irreducible]
def a12853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12791 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12831 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12852 ^ 1)
theorem ha12853 : a12853.IsHomogeneous 184 := by
  unfold a12853
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12791.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12831.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12852.pow 1)))

@[irreducible]
def a12854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12792 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12832 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12853 ^ 1)
theorem ha12854 : a12854.IsHomogeneous 190 := by
  unfold a12854
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12792.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12832.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12853.pow 1)))

@[irreducible]
def a12855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12793 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12854 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12833 ^ 1)
theorem ha12855 : a12855.IsHomogeneous 196 := by
  unfold a12855
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12793.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12854.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12833.pow 1)))

@[irreducible]
def a12856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12855 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a12841 ^ 1)
theorem ha12856 : a12856.IsHomogeneous 202 := by
  unfold a12856
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12823.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12855.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha12841.pow 1)))

@[irreducible]
def a12857 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a07148 ^ 1)
theorem ha12857 : a12857.IsHomogeneous 300 := by
  unfold a12857
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12856.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha07148.pow 1)))

@[irreducible]
def a12858 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12757 ^ 1)
theorem ha12858 : a12858.IsHomogeneous 398 := by
  unfold a12858
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12857.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12757.pow 1)))

@[irreducible]
def a12859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12758 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12858 ^ 1)
theorem ha12859 : a12859.IsHomogeneous 496 := by
  unfold a12859
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12758.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12858.pow 1)))

@[irreducible]
def a12860 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12859 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12759 ^ 1)
theorem ha12860 : a12860.IsHomogeneous 594 := by
  unfold a12860
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12859.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12759.pow 1)))

@[irreducible]
def a12861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12763 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12860 ^ 1)
theorem ha12861 : a12861.IsHomogeneous 691 := by
  unfold a12861
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12763.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12860.pow 1)))

@[irreducible]
def a12862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01861 ^ 1 * a03831 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01858 ^ 1 * a03837 ^ 1)
theorem ha12862 : a12862.IsHomogeneous 484 := by
  unfold a12862
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01861.pow 1)).mul (ha03831.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01858.pow 1)).mul (ha03837.pow 1)))

@[irreducible]
def a12863 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1 * a03831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a07165 ^ 1)
theorem ha12863 : a12863.IsHomogeneous 582 := by
  unfold a12863
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).mul (ha03831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha07165.pow 1)))

@[irreducible]
def a12864 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12862 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12863 ^ 1)
theorem ha12864 : a12864.IsHomogeneous 582 := by
  unfold a12864
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12862.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12863.pow 1)))

@[irreducible]
def a12865 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a07174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01858 ^ 1 * a03837 ^ 1)
theorem ha12865 : a12865.IsHomogeneous 386 := by
  unfold a12865
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha07174.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01858.pow 1)).mul (ha03837.pow 1)))

@[irreducible]
def a12866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12862 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12865 ^ 1)
theorem ha12866 : a12866.IsHomogeneous 484 := by
  unfold a12866
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12862.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12865.pow 1)))

@[irreducible]
def a12867 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12864 ^ 1)
theorem ha12867 : a12867.IsHomogeneous 582 := by
  unfold a12867
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12866.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12864.pow 1)))

@[irreducible]
def a12868 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a03837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01861 ^ 1 * a03828 ^ 1)
theorem ha12868 : a12868.IsHomogeneous 387 := by
  unfold a12868
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha03837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01861.pow 1)).mul (ha03828.pow 1)))

@[irreducible]
def a12869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a07160 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1 * a03828 ^ 1)
theorem ha12869 : a12869.IsHomogeneous 485 := by
  unfold a12869
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha07160.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).mul (ha03828.pow 1)))

@[irreducible]
def a12870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12869 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12868 ^ 1)
theorem ha12870 : a12870.IsHomogeneous 485 := by
  unfold a12870
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12869.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12868.pow 1)))

@[irreducible]
def a12871 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01861 ^ 1)
theorem ha12871 : a12871.IsHomogeneous 290 := by
  unfold a12871
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01861.pow 1)))

@[irreducible]
def a12872 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a07158 ^ 1)
theorem ha12872 : a12872.IsHomogeneous 388 := by
  unfold a12872
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha07158.pow 1)))

@[irreducible]
def a12873 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12872 ^ 1)
theorem ha12873 : a12873.IsHomogeneous 388 := by
  unfold a12873
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12871.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12872.pow 1)))

@[irreducible]
def a12874 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00789 ^ 1)
theorem ha12874 : a12874.IsHomogeneous 291 := by
  unfold a12874
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00789.pow 1)))

@[irreducible]
def a12875 : Poly := (C ((-5 : ℂ) / (216 : ℂ)) * a00789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 2)
theorem ha12875 : a12875.IsHomogeneous 194 := by
  unfold a12875
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (216 : ℂ))).mul (ha00789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a12876 : Poly := (C ((-216 : ℂ) / (5 : ℂ)) * a12875 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1)
theorem ha12876 : a12876.IsHomogeneous 194 := by
  unfold a12876
  exact (((isHomogeneous_C (σ := Fin 6) ((-216 : ℂ) / (5 : ℂ))).mul (ha12875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)))

@[irreducible]
def a12877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a12876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12874 ^ 1)
theorem ha12877 : a12877.IsHomogeneous 291 := by
  unfold a12877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha12876.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12874.pow 1)))

@[irreducible]
def a12878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a12877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a07158 ^ 1)
theorem ha12878 : a12878.IsHomogeneous 388 := by
  unfold a12878
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha12877.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha07158.pow 1)))

@[irreducible]
def a12879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12872 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12878 ^ 1)
theorem ha12879 : a12879.IsHomogeneous 388 := by
  unfold a12879
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12872.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12878.pow 1)))

@[irreducible]
def a12880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12879 ^ 1)
theorem ha12880 : a12880.IsHomogeneous 388 := by
  unfold a12880
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12873.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12879.pow 1)))

@[irreducible]
def a12881 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00789 ^ 1 * a07160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a12880 ^ 1)
theorem ha12881 : a12881.IsHomogeneous 485 := by
  unfold a12881
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00789.pow 1)).mul (ha07160.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha12880.pow 1)))

@[irreducible]
def a12882 : Poly := (C ((-36 : ℂ) / (1 : ℂ)) * a12881 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12869 ^ 1)
theorem ha12882 : a12882.IsHomogeneous 485 := by
  unfold a12882
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (1 : ℂ))).mul (ha12881.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12869.pow 1)))

@[irreducible]
def a12883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12882 ^ 1)
theorem ha12883 : a12883.IsHomogeneous 485 := by
  unfold a12883
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12870.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12882.pow 1)))

@[irreducible]
def a12884 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a03837 ^ 1)
theorem ha12884 : a12884.IsHomogeneous 289 := by
  unfold a12884
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07174.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha03837.pow 1)))

@[irreducible]
def a12885 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12868 ^ 1)
theorem ha12885 : a12885.IsHomogeneous 387 := by
  unfold a12885
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12868.pow 1)))

@[irreducible]
def a12886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12870 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12885 ^ 1)
theorem ha12886 : a12886.IsHomogeneous 485 := by
  unfold a12886
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12870.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12885.pow 1)))

@[irreducible]
def a12887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12886 ^ 1)
theorem ha12887 : a12887.IsHomogeneous 485 := by
  unfold a12887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12886.pow 1)))

@[irreducible]
def a12888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a12887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a07165 ^ 1)
theorem ha12888 : a12888.IsHomogeneous 582 := by
  unfold a12888
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha12887.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha07165.pow 1)))

@[irreducible]
def a12889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12863 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12888 ^ 1)
theorem ha12889 : a12889.IsHomogeneous 582 := by
  unfold a12889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12863.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12888.pow 1)))

@[irreducible]
def a12890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12889 ^ 1)
theorem ha12890 : a12890.IsHomogeneous 582 := by
  unfold a12890
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12864.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12889.pow 1)))

@[irreducible]
def a12891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12890 ^ 1)
theorem ha12891 : a12891.IsHomogeneous 582 := by
  unfold a12891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12867.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12890.pow 1)))

@[irreducible]
def a12892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00773 ^ 1 * a03764 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a01822 ^ 2)
theorem ha12892 : a12892.IsHomogeneous 190 := by
  unfold a12892
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00773.pow 1)).mul (ha03764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha01822.pow 2)))

@[irreducible]
def a12893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a07048 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00773 ^ 1 * a03764 ^ 1)
theorem ha12893 : a12893.IsHomogeneous 190 := by
  unfold a12893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha07048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00773.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a12894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12892 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12893 ^ 1)
theorem ha12894 : a12894.IsHomogeneous 190 := by
  unfold a12894
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12893.pow 1)))

@[irreducible]
def a12895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12892 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12894 ^ 1)
theorem ha12895 : a12895.IsHomogeneous 190 := by
  unfold a12895
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12894.pow 1)))

@[irreducible]
def a12896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12701 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a07048 ^ 1)
theorem ha12896 : a12896.IsHomogeneous 190 := by
  unfold a12896
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12701.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha07048.pow 1)))

@[irreducible]
def a12897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12893 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a12896 ^ 1)
theorem ha12897 : a12897.IsHomogeneous 190 := by
  unfold a12897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha12896.pow 1)))

@[irreducible]
def a12898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12894 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12897 ^ 1)
theorem ha12898 : a12898.IsHomogeneous 190 := by
  unfold a12898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12894.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12897.pow 1)))

@[irreducible]
def a12899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12895 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12898 ^ 1)
theorem ha12899 : a12899.IsHomogeneous 190 := by
  unfold a12899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12895.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12898.pow 1)))

@[irreducible]
def a12900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12895 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12899 ^ 1)
theorem ha12900 : a12900.IsHomogeneous 190 := by
  unfold a12900
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12895.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12899.pow 1)))

@[irreducible]
def a12901 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a07174 ^ 1)
theorem ha12901 : a12901.IsHomogeneous 288 := by
  unfold a12901
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12900.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha07174.pow 1)))

@[irreducible]
def a12902 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12865 ^ 1)
theorem ha12902 : a12902.IsHomogeneous 386 := by
  unfold a12902
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12865.pow 1)))

@[irreducible]
def a12903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12866 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12902 ^ 1)
theorem ha12903 : a12903.IsHomogeneous 484 := by
  unfold a12903
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12866.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12902.pow 1)))

@[irreducible]
def a12904 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a12903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12867 ^ 1)
theorem ha12904 : a12904.IsHomogeneous 582 := by
  unfold a12904
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha12903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12867.pow 1)))

@[irreducible]
def a12905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12904 ^ 1)
theorem ha12905 : a12905.IsHomogeneous 582 := by
  unfold a12905
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12904.pow 1)))

@[irreducible]
def a12906 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a12905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00290 ^ 1 * a07178 ^ 1)
theorem ha12906 : a12906.IsHomogeneous 703 := by
  unfold a12906
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12905.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00290.pow 1)).mul (ha07178.pow 1)))

@[irreducible]
def a12907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12760 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a12906 ^ 1)
theorem ha12907 : a12907.IsHomogeneous 764 := by
  unfold a12907
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12760.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha12906.pow 1)))

@[irreducible]
def a12908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12761 ^ 1)
theorem ha12908 : a12908.IsHomogeneous 770 := by
  unfold a12908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12907.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12761.pow 1)))

@[irreducible]
def a12909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12908 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12762 ^ 1)
theorem ha12909 : a12909.IsHomogeneous 776 := by
  unfold a12909
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12908.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12762.pow 1)))

@[irreducible]
def a12910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12909 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12763 ^ 1)
theorem ha12910 : a12910.IsHomogeneous 782 := by
  unfold a12910
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12909.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12763.pow 1)))

@[irreducible]
def a12911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12910 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a12861 ^ 1)
theorem ha12911 : a12911.IsHomogeneous 788 := by
  unfold a12911
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12910.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha12861.pow 1)))

@[irreducible]
def a12912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a07183 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12911 ^ 1)
theorem ha12912 : a12912.IsHomogeneous 903 := by
  unfold a12912
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha07183.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12911.pow 1)))

@[irreducible]
def a12913 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12727 ^ 1)
theorem ha12913 : a12913.IsHomogeneous 1018 := by
  unfold a12913
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12727.pow 1)))

@[irreducible]
def a12914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12728 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12913 ^ 1)
theorem ha12914 : a12914.IsHomogeneous 1133 := by
  unfold a12914
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12728.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12913.pow 1)))

@[irreducible]
def a12915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12729 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12914 ^ 1)
theorem ha12915 : a12915.IsHomogeneous 1248 := by
  unfold a12915
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12729.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12914.pow 1)))

@[irreducible]
def a12916 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00124 ^ 1 * a12915 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12753 ^ 1)
theorem ha12916 : a12916.IsHomogeneous 1308 := by
  unfold a12916
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00124.pow 1)).mul (ha12915.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12753.pow 1)))

@[irreducible]
def a12917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1 * a07187 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a12916 ^ 1)
theorem ha12917 : a12917.IsHomogeneous 1374 := by
  unfold a12917
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).mul (ha07187.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha12916.pow 1)))

@[irreducible]
def a12918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12243 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a12917 ^ 1)
theorem ha12918 : a12918.IsHomogeneous 1416 := by
  unfold a12918
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12243.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha12917.pow 1)))

@[irreducible]
def a12919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12244 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12918 ^ 1)
theorem ha12919 : a12919.IsHomogeneous 1458 := by
  unfold a12919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12244.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12918.pow 1)))

@[irreducible]
def a12920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12919 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12245 ^ 1)
theorem ha12920 : a12920.IsHomogeneous 1500 := by
  unfold a12920
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12919.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12245.pow 1)))

@[irreducible]
def a12921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12246 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a12920 ^ 1)
theorem ha12921 : a12921.IsHomogeneous 1542 := by
  unfold a12921
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12246.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha12920.pow 1)))

@[irreducible]
def a12922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12723 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12921 ^ 1)
theorem ha12922 : a12922.IsHomogeneous 1584 := by
  unfold a12922
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12723.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12921.pow 1)))

@[irreducible]
def a12923 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00294 ^ 1 * a07192 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a12922 ^ 1)
theorem ha12923 : a12923.IsHomogeneous 1689 := by
  unfold a12923
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00294.pow 1)).mul (ha07192.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha12922.pow 1)))

@[irreducible]
def a12924 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12923 ^ 1)
theorem ha12924 : a12924.IsHomogeneous 1689 := by
  unfold a12924
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12923.pow 1)))

@[irreducible]
def a12925 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12924 ^ 1)
theorem ha12925 : a12925.IsHomogeneous 1689 := by
  unfold a12925
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12924.pow 1)))

@[irreducible]
def a12926 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12925 ^ 1)
theorem ha12926 : a12926.IsHomogeneous 1689 := by
  unfold a12926
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12925.pow 1)))

@[irreducible]
def a12927 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12926 ^ 1)
theorem ha12927 : a12927.IsHomogeneous 1689 := by
  unfold a12927
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12236.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12926.pow 1)))

@[irreducible]
def a12928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01702 ^ 1 * a01877 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00798 ^ 1 * a03562 ^ 1)
theorem ha12928 : a12928.IsHomogeneous 131 := by
  unfold a12928
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01702.pow 1)).mul (ha01877.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00798.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a12929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01702 ^ 1 * a01877 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00712 ^ 1 * a03861 ^ 1)
theorem ha12929 : a12929.IsHomogeneous 130 := by
  unfold a12929
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01702.pow 1)).mul (ha01877.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a12930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12929 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12928 ^ 1)
theorem ha12930 : a12930.IsHomogeneous 131 := by
  unfold a12930
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12929.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12928.pow 1)))

@[irreducible]
def a12931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00293 ^ 1 * a06725 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00798 ^ 1 * a03562 ^ 1)
theorem ha12931 : a12931.IsHomogeneous 131 := by
  unfold a12931
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00293.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00798.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a12932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12928 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a12931 ^ 1)
theorem ha12932 : a12932.IsHomogeneous 131 := by
  unfold a12932
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha12931.pow 1)))

@[irreducible]
def a12933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12932 ^ 1)
theorem ha12933 : a12933.IsHomogeneous 131 := by
  unfold a12933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12932.pow 1)))

@[irreducible]
def a12934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a03861 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a07207 ^ 1)
theorem ha12934 : a12934.IsHomogeneous 125 := by
  unfold a12934
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha03861.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha07207.pow 1)))

@[irreducible]
def a12935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12929 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12934 ^ 1)
theorem ha12935 : a12935.IsHomogeneous 131 := by
  unfold a12935
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12934.pow 1)))

@[irreducible]
def a12936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12935 ^ 1)
theorem ha12936 : a12936.IsHomogeneous 131 := by
  unfold a12936
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12935.pow 1)))

@[irreducible]
def a12937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12936 ^ 1)
theorem ha12937 : a12937.IsHomogeneous 131 := by
  unfold a12937
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12933.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12936.pow 1)))

@[irreducible]
def a12938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a06725 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00125 ^ 1 * a12210 ^ 1)
theorem ha12938 : a12938.IsHomogeneous 123 := by
  unfold a12938
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha06725.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha12210.pow 1)))

@[irreducible]
def a12939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a12938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12931 ^ 1)
theorem ha12939 : a12939.IsHomogeneous 131 := by
  unfold a12939
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha12938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12931.pow 1)))

@[irreducible]
def a12940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12932 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a12939 ^ 1)
theorem ha12940 : a12940.IsHomogeneous 131 := by
  unfold a12940
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha12939.pow 1)))

@[irreducible]
def a12941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12940 ^ 1)
theorem ha12941 : a12941.IsHomogeneous 131 := by
  unfold a12941
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12933.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12940.pow 1)))

@[irreducible]
def a12942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12937 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12941 ^ 1)
theorem ha12942 : a12942.IsHomogeneous 131 := by
  unfold a12942
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12937.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12941.pow 1)))

@[irreducible]
def a12943 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a11520 ^ 1) + (C ((-1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a11787 ^ 1) + (C ((-1 : ℂ) / (4608 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 5 * a00005 ^ 4 * a12210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 4 * a11222 ^ 1) + (C ((1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a12171 ^ 1)
theorem ha12943 : a12943.IsHomogeneous 76 := by
  unfold a12943
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha11520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha11787.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4608 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha12210.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 4)).mul (ha11222.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha12171.pow 1)))

@[irreducible]
def a12944 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a12943 ^ 1)
theorem ha12944 : a12944.IsHomogeneous 119 := by
  unfold a12944
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07207.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha12943.pow 1)))

@[irreducible]
def a12945 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a12944 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12934 ^ 1)
theorem ha12945 : a12945.IsHomogeneous 125 := by
  unfold a12945
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha12944.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12934.pow 1)))

@[irreducible]
def a12946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12945 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a12935 ^ 1)
theorem ha12946 : a12946.IsHomogeneous 131 := by
  unfold a12946
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12945.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha12935.pow 1)))

@[irreducible]
def a12947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12936 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12946 ^ 1)
theorem ha12947 : a12947.IsHomogeneous 131 := by
  unfold a12947
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12946.pow 1)))

@[irreducible]
def a12948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12937 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12947 ^ 1)
theorem ha12948 : a12948.IsHomogeneous 131 := by
  unfold a12948
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12937.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12947.pow 1)))

@[irreducible]
def a12949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12942 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12948 ^ 1)
theorem ha12949 : a12949.IsHomogeneous 131 := by
  unfold a12949
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12942.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12948.pow 1)))

@[irreducible]
def a12950 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a07212 ^ 1)
theorem ha12950 : a12950.IsHomogeneous 416 := by
  unfold a12950
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha07212.pow 1)))

@[irreducible]
def a12951 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12233 ^ 1)
theorem ha12951 : a12951.IsHomogeneous 671 := by
  unfold a12951
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12233.pow 1)))

@[irreducible]
def a12952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12951 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12234 ^ 1)
theorem ha12952 : a12952.IsHomogeneous 926 := by
  unfold a12952
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12951.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12234.pow 1)))

@[irreducible]
def a12953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12235 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12952 ^ 1)
theorem ha12953 : a12953.IsHomogeneous 1181 := by
  unfold a12953
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12235.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12952.pow 1)))

@[irreducible]
def a12954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12236 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12953 ^ 1)
theorem ha12954 : a12954.IsHomogeneous 1435 := by
  unfold a12954
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12236.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12953.pow 1)))

@[irreducible]
def a12955 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12954 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12927 ^ 1)
theorem ha12955 : a12955.IsHomogeneous 1689 := by
  unfold a12955
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12954.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12927.pow 1)))

@[irreducible]
def a12956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a07217 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a12955 ^ 1)
theorem ha12956 : a12956.IsHomogeneous 1768 := by
  unfold a12956
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha07217.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha12955.pow 1)))

@[irreducible]
def a12957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10723 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a12956 ^ 1)
theorem ha12957 : a12957.IsHomogeneous 1847 := by
  unfold a12957
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10723.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha12956.pow 1)))

@[irreducible]
def a12958 : Poly := (C ((-192 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a12957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10724 ^ 1)
theorem ha12958 : a12958.IsHomogeneous 1926 := by
  unfold a12958
  exact ((((isHomogeneous_C (σ := Fin 6) ((-192 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha12957.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10724.pow 1)))

@[irreducible]
def a12959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10725 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a12958 ^ 1)
theorem ha12959 : a12959.IsHomogeneous 2005 := by
  unfold a12959
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha12958.pow 1)))

@[irreducible]
def a12960 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a12959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10726 ^ 1)
theorem ha12960 : a12960.IsHomogeneous 2084 := by
  unfold a12960
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha12959.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10726.pow 1)))

@[irreducible]
def a12961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12226 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a12960 ^ 1)
theorem ha12961 : a12961.IsHomogeneous 2163 := by
  unfold a12961
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12226.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha12960.pow 1)))

@[irreducible]
def a12962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a07222 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a12961 ^ 1)
theorem ha12962 : a12962.IsHomogeneous 2271 := by
  unfold a12962
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha07222.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha12961.pow 1)))

@[irreducible]
def a12963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10710 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a12962 ^ 1)
theorem ha12963 : a12963.IsHomogeneous 2361 := by
  unfold a12963
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10710.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha12962.pow 1)))

@[irreducible]
def a12964 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10711 ^ 1)
theorem ha12964 : a12964.IsHomogeneous 2421 := by
  unfold a12964
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12963.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10711.pow 1)))

@[irreducible]
def a12965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10712 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12964 ^ 1)
theorem ha12965 : a12965.IsHomogeneous 2481 := by
  unfold a12965
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12964.pow 1)))

@[irreducible]
def a12966 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10716 ^ 1)
theorem ha12966 : a12966.IsHomogeneous 2541 := by
  unfold a12966
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12965.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10716.pow 1)))

@[irreducible]
def a12967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01926 ^ 1 * a01946 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a00834 ^ 1 * a03937 ^ 1)
theorem ha12967 : a12967.IsHomogeneous 354 := by
  unfold a12967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01926.pow 1)).mul (ha01946.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00834.pow 1)).mul (ha03937.pow 1)))

@[irreducible]
def a12968 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01926 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00825 ^ 1 * a03974 ^ 1)
theorem ha12968 : a12968.IsHomogeneous 414 := by
  unfold a12968
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01926.pow 1)).mul (ha01946.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00825.pow 1)).mul (ha03974.pow 1)))

@[irreducible]
def a12969 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12968 ^ 1)
theorem ha12969 : a12969.IsHomogeneous 414 := by
  unfold a12969
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12968.pow 1)))

@[irreducible]
def a12970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a03937 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a07317 ^ 1)
theorem ha12970 : a12970.IsHomogeneous 291 := by
  unfold a12970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha03937.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha07317.pow 1)))

@[irreducible]
def a12971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12967 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a12970 ^ 1)
theorem ha12971 : a12971.IsHomogeneous 354 := by
  unfold a12971
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12967.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12970.pow 1)))

@[irreducible]
def a12972 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12971 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12969 ^ 1)
theorem ha12972 : a12972.IsHomogeneous 414 := by
  unfold a12972
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12971.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12969.pow 1)))

@[irreducible]
def a12973 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00825 ^ 1 * a03974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00304 ^ 1 * a07377 ^ 1)
theorem ha12973 : a12973.IsHomogeneous 474 := by
  unfold a12973
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00825.pow 1)).mul (ha03974.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00304.pow 1)).mul (ha07377.pow 1)))

@[irreducible]
def a12974 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12968 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12973 ^ 1)
theorem ha12974 : a12974.IsHomogeneous 474 := by
  unfold a12974
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12968.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12973.pow 1)))

@[irreducible]
def a12975 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12969 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12974 ^ 1)
theorem ha12975 : a12975.IsHomogeneous 474 := by
  unfold a12975
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12969.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12974.pow 1)))

@[irreducible]
def a12976 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a12972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12975 ^ 1)
theorem ha12976 : a12976.IsHomogeneous 474 := by
  unfold a12976
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha12972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12975.pow 1)))

@[irreducible]
def a12977 : Poly := (C ((-35 : ℂ) / (486 : ℂ)) * a00014 ^ 1 * a00823 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01896 ^ 1 * a01923 ^ 1)
theorem ha12977 : a12977.IsHomogeneous 153 := by
  unfold a12977
  exact (((((isHomogeneous_C (σ := Fin 6) ((-35 : ℂ) / (486 : ℂ))).mul (ha00014.pow 1)).mul (ha00823.pow 1)).mul (ha03890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01896.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a12978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a03933 ^ 1)
theorem ha12978 : a12978.IsHomogeneous 156 := by
  unfold a12978
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).mul (ha01923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha03933.pow 1)))

@[irreducible]
def a12979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12977 ^ 1)
theorem ha12979 : a12979.IsHomogeneous 159 := by
  unfold a12979
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12977.pow 1)))

@[irreducible]
def a12980 : Poly := (C ((-10 : ℂ) / (3 : ℂ)) * a00823 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00303 ^ 1 * a07248 ^ 1)
theorem ha12980 : a12980.IsHomogeneous 147 := by
  unfold a12980
  exact ((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (3 : ℂ))).mul (ha00823.pow 1)).mul (ha03890.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a12981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12977 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a00014 ^ 1 * a12980 ^ 1)
theorem ha12981 : a12981.IsHomogeneous 153 := by
  unfold a12981
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12977.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha00014.pow 1)).mul (ha12980.pow 1)))

@[irreducible]
def a12982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12981 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12979 ^ 1)
theorem ha12982 : a12982.IsHomogeneous 159 := by
  unfold a12982
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12979.pow 1)))

@[irreducible]
def a12983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a03933 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00298 ^ 1 * a07312 ^ 1)
theorem ha12983 : a12983.IsHomogeneous 165 := by
  unfold a12983
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha03933.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00298.pow 1)).mul (ha07312.pow 1)))

@[irreducible]
def a12984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12983 ^ 1)
theorem ha12984 : a12984.IsHomogeneous 165 := by
  unfold a12984
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12978.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12983.pow 1)))

@[irreducible]
def a12985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12984 ^ 1)
theorem ha12985 : a12985.IsHomogeneous 165 := by
  unfold a12985
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12979.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12984.pow 1)))

@[irreducible]
def a12986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12985 ^ 1)
theorem ha12986 : a12986.IsHomogeneous 165 := by
  unfold a12986
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12985.pow 1)))

@[irreducible]
def a12987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a04086 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02008 ^ 1)
theorem ha12987 : a12987.IsHomogeneous 24 := by
  unfold a12987
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02008.pow 1)))

@[irreducible]
def a12988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12987 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06361 ^ 1)
theorem ha12988 : a12988.IsHomogeneous 24 := by
  unfold a12988
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12987.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06361.pow 1)))

@[irreducible]
def a12989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12988 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06362 ^ 1)
theorem ha12989 : a12989.IsHomogeneous 24 := by
  unfold a12989
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06362.pow 1)))

@[irreducible]
def a12990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12989 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06363 ^ 1)
theorem ha12990 : a12990.IsHomogeneous 24 := by
  unfold a12990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12989.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06363.pow 1)))

@[irreducible]
def a12991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06364 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a12990 ^ 1)
theorem ha12991 : a12991.IsHomogeneous 24 := by
  unfold a12991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha12990.pow 1)))

@[irreducible]
def a12992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a07558 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a04086 ^ 1)
theorem ha12992 : a12992.IsHomogeneous 24 := by
  unfold a12992
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a12993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12987 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12992 ^ 1)
theorem ha12993 : a12993.IsHomogeneous 24 := by
  unfold a12993
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12987.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12992.pow 1)))

@[irreducible]
def a12994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12993 ^ 1)
theorem ha12994 : a12994.IsHomogeneous 24 := by
  unfold a12994
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12988.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12993.pow 1)))

@[irreducible]
def a12995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12989 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12994 ^ 1)
theorem ha12995 : a12995.IsHomogeneous 24 := by
  unfold a12995
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12989.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12994.pow 1)))

@[irreducible]
def a12996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12990 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12995 ^ 1)
theorem ha12996 : a12996.IsHomogeneous 24 := by
  unfold a12996
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12990.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12995.pow 1)))

@[irreducible]
def a12997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12991 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a12996 ^ 1)
theorem ha12997 : a12997.IsHomogeneous 24 := by
  unfold a12997
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha12996.pow 1)))

@[irreducible]
def a12998 : Poly := (C ((-7 : ℂ) / (9 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11895 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12997 ^ 1)
theorem ha12998 : a12998.IsHomogeneous 24 := by
  unfold a12998
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (9 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11895.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12997.pow 1)))

@[irreducible]
def a12999 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a12998 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a07248 ^ 1)
theorem ha12999 : a12999.IsHomogeneous 138 := by
  unfold a12999
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha12998.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a13000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12999 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12980 ^ 1)
theorem ha13000 : a13000.IsHomogeneous 147 := by
  unfold a13000
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12980.pow 1)))

@[irreducible]
def a13001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12981 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a00014 ^ 1 * a13000 ^ 1)
theorem ha13001 : a13001.IsHomogeneous 153 := by
  unfold a13001
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12981.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha00014.pow 1)).mul (ha13000.pow 1)))

@[irreducible]
def a13002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13001 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12982 ^ 1)
theorem ha13002 : a13002.IsHomogeneous 159 := by
  unfold a13002
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12982.pow 1)))

@[irreducible]
def a13003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13002 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12986 ^ 1)
theorem ha13003 : a13003.IsHomogeneous 165 := by
  unfold a13003
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13002.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12986.pow 1)))

@[irreducible]
def a13004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00821 ^ 1 * a03803 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01841 ^ 1 * a01920 ^ 1)
theorem ha13004 : a13004.IsHomogeneous 138 := by
  unfold a13004
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00821.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01841.pow 1)).mul (ha01920.pow 1)))

@[irreducible]
def a13005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01841 ^ 1 * a01920 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a03929 ^ 1)
theorem ha13005 : a13005.IsHomogeneous 135 := by
  unfold a13005
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01841.pow 1)).mul (ha01920.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha03929.pow 1)))

@[irreducible]
def a13006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13004 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13005 ^ 1)
theorem ha13006 : a13006.IsHomogeneous 138 := by
  unfold a13006
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13005.pow 1)))

@[irreducible]
def a13007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00302 ^ 1 * a07120 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00821 ^ 1 * a03803 ^ 1)
theorem ha13007 : a13007.IsHomogeneous 138 := by
  unfold a13007
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00302.pow 1)).mul (ha07120.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00821.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a13008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13004 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13007 ^ 1)
theorem ha13008 : a13008.IsHomogeneous 138 := by
  unfold a13008
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13007.pow 1)))

@[irreducible]
def a13009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13008 ^ 1)
theorem ha13009 : a13009.IsHomogeneous 138 := by
  unfold a13009
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13008.pow 1)))

@[irreducible]
def a13010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a03929 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a07307 ^ 1)
theorem ha13010 : a13010.IsHomogeneous 129 := by
  unfold a13010
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha03929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha07307.pow 1)))

@[irreducible]
def a13011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13005 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a13010 ^ 1)
theorem ha13011 : a13011.IsHomogeneous 135 := by
  unfold a13011
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13005.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha13010.pow 1)))

@[irreducible]
def a13012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13006 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13011 ^ 1)
theorem ha13012 : a13012.IsHomogeneous 138 := by
  unfold a13012
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13011.pow 1)))

@[irreducible]
def a13013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13012 ^ 1)
theorem ha13013 : a13013.IsHomogeneous 138 := by
  unfold a13013
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13012.pow 1)))

@[irreducible]
def a13014 : Poly := (C ((-6 : ℂ) / (25 : ℂ)) * a00302 ^ 1 * a07120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a12818 ^ 1)
theorem ha13014 : a13014.IsHomogeneous 138 := by
  unfold a13014
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (25 : ℂ))).mul (ha00302.pow 1)).mul (ha07120.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha12818.pow 1)))

@[irreducible]
def a13015 : Poly := (C ((-25 : ℂ) / (6 : ℂ)) * a13014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13007 ^ 1)
theorem ha13015 : a13015.IsHomogeneous 138 := by
  unfold a13015
  exact (((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (6 : ℂ))).mul (ha13014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13007.pow 1)))

@[irreducible]
def a13016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13008 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13015 ^ 1)
theorem ha13016 : a13016.IsHomogeneous 138 := by
  unfold a13016
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13015.pow 1)))

@[irreducible]
def a13017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13016 ^ 1)
theorem ha13017 : a13017.IsHomogeneous 138 := by
  unfold a13017
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13016.pow 1)))

@[irreducible]
def a13018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13017 ^ 1)
theorem ha13018 : a13018.IsHomogeneous 138 := by
  unfold a13018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13017.pow 1)))

@[irreducible]
def a13019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01903 ^ 1 * a01917 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a00819 ^ 1 * a03811 ^ 1)
theorem ha13019 : a13019.IsHomogeneous 120 := by
  unfold a13019
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01903.pow 1)).mul (ha01917.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a13020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a03925 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01903 ^ 1 * a01917 ^ 1)
theorem ha13020 : a13020.IsHomogeneous 120 := by
  unfold a13020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha03925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01903.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a13021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13019 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13020 ^ 1)
theorem ha13021 : a13021.IsHomogeneous 120 := by
  unfold a13021
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13020.pow 1)))

@[irreducible]
def a13022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a07132 ^ 1)
theorem ha13022 : a13022.IsHomogeneous 108 := by
  unfold a13022
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha03811.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha07132.pow 1)))

@[irreducible]
def a13023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13019 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a13022 ^ 1)
theorem ha13023 : a13023.IsHomogeneous 120 := by
  unfold a13023
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13019.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha13022.pow 1)))

@[irreducible]
def a13024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13021 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13023 ^ 1)
theorem ha13024 : a13024.IsHomogeneous 120 := by
  unfold a13024
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13023.pow 1)))

@[irreducible]
def a13025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a07302 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00812 ^ 1 * a03925 ^ 1)
theorem ha13025 : a13025.IsHomogeneous 120 := by
  unfold a13025
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha07302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00812.pow 1)).mul (ha03925.pow 1)))

@[irreducible]
def a13026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13020 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a13025 ^ 1)
theorem ha13026 : a13026.IsHomogeneous 120 := by
  unfold a13026
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha13025.pow 1)))

@[irreducible]
def a13027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13021 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13026 ^ 1)
theorem ha13027 : a13027.IsHomogeneous 120 := by
  unfold a13027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13026.pow 1)))

@[irreducible]
def a13028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13027 ^ 1)
theorem ha13028 : a13028.IsHomogeneous 120 := by
  unfold a13028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13027.pow 1)))

@[irreducible]
def a13029 : Poly := (C ((-14 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a12835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a07132 ^ 1)
theorem ha13029 : a13029.IsHomogeneous 102 := by
  unfold a13029
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha12835.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha07132.pow 1)))

@[irreducible]
def a13030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13022 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a13029 ^ 1)
theorem ha13030 : a13030.IsHomogeneous 108 := by
  unfold a13030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13022.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha13029.pow 1)))

@[irreducible]
def a13031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13023 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a13030 ^ 1)
theorem ha13031 : a13031.IsHomogeneous 120 := by
  unfold a13031
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13023.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha13030.pow 1)))

@[irreducible]
def a13032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13031 ^ 1)
theorem ha13032 : a13032.IsHomogeneous 120 := by
  unfold a13032
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13031.pow 1)))

@[irreducible]
def a13033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13032 ^ 1)
theorem ha13033 : a13033.IsHomogeneous 120 := by
  unfold a13033
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13032.pow 1)))

@[irreducible]
def a13034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00817 ^ 1 * a03562 ^ 1) + (C ((81 : ℂ) / (4 : ℂ)) * a01702 ^ 1 * a01914 ^ 1)
theorem ha13034 : a13034.IsHomogeneous 102 := by
  unfold a13034
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00817.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (4 : ℂ))).mul (ha01702.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a13035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00712 ^ 1 * a03921 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01702 ^ 1 * a01914 ^ 1)
theorem ha13035 : a13035.IsHomogeneous 102 := by
  unfold a13035
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha03921.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01702.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a13036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13034 ^ 1) + (C ((243 : ℂ) / (5 : ℂ)) * a13035 ^ 1)
theorem ha13036 : a13036.IsHomogeneous 102 := by
  unfold a13036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13034.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (5 : ℂ))).mul (ha13035.pow 1)))

@[irreducible]
def a13037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a06725 ^ 1) + (C ((10 : ℂ) / (27 : ℂ)) * a00817 ^ 1 * a03562 ^ 1)
theorem ha13037 : a13037.IsHomogeneous 102 := by
  unfold a13037
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (27 : ℂ))).mul (ha00817.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a13038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13034 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a13037 ^ 1)
theorem ha13038 : a13038.IsHomogeneous 102 := by
  unfold a13038
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13034.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha13037.pow 1)))

@[irreducible]
def a13039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13036 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13038 ^ 1)
theorem ha13039 : a13039.IsHomogeneous 102 := by
  unfold a13039
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13036.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13038.pow 1)))

@[irreducible]
def a13040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a03921 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a07297 ^ 1)
theorem ha13040 : a13040.IsHomogeneous 96 := by
  unfold a13040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha03921.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha07297.pow 1)))

@[irreducible]
def a13041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13040 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13035 ^ 1)
theorem ha13041 : a13041.IsHomogeneous 102 := by
  unfold a13041
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13035.pow 1)))

@[irreducible]
def a13042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13036 ^ 1) + (C ((243 : ℂ) / (5 : ℂ)) * a13041 ^ 1)
theorem ha13042 : a13042.IsHomogeneous 102 := by
  unfold a13042
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13036.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (5 : ℂ))).mul (ha13041.pow 1)))

@[irreducible]
def a13043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13039 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13042 ^ 1)
theorem ha13043 : a13043.IsHomogeneous 102 := by
  unfold a13043
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13042.pow 1)))

@[irreducible]
def a13044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a12210 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a06725 ^ 1)
theorem ha13044 : a13044.IsHomogeneous 102 := by
  unfold a13044
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha12210.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13037 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a13044 ^ 1)
theorem ha13045 : a13045.IsHomogeneous 102 := by
  unfold a13045
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13037.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha13044.pow 1)))

@[irreducible]
def a13046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13038 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a13045 ^ 1)
theorem ha13046 : a13046.IsHomogeneous 102 := by
  unfold a13046
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13038.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha13045.pow 1)))

@[irreducible]
def a13047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13039 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13046 ^ 1)
theorem ha13047 : a13047.IsHomogeneous 102 := by
  unfold a13047
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13046.pow 1)))

@[irreducible]
def a13048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13047 ^ 1)
theorem ha13048 : a13048.IsHomogeneous 102 := by
  unfold a13048
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13043.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13047.pow 1)))

@[irreducible]
def a13049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01896 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02008 ^ 1)
theorem ha13049 : a13049.IsHomogeneous 48 := by
  unfold a13049
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01896.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03890 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00865 ^ 1 * a01896 ^ 1)
theorem ha13050 : a13050.IsHomogeneous 48 := by
  unfold a13050
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00865.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a13051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13049 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a13050 ^ 1)
theorem ha13051 : a13051.IsHomogeneous 48 := by
  unfold a13051
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13049.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha13050.pow 1)))

@[irreducible]
def a13052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02008 ^ 1)
theorem ha13052 : a13052.IsHomogeneous 48 := by
  unfold a13052
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13049 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a13052 ^ 1)
theorem ha13053 : a13053.IsHomogeneous 48 := by
  unfold a13053
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13049.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha13052.pow 1)))

@[irreducible]
def a13054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13053 ^ 1)
theorem ha13054 : a13054.IsHomogeneous 48 := by
  unfold a13054
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13053.pow 1)))

@[irreducible]
def a13055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03890 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a07248 ^ 1)
theorem ha13055 : a13055.IsHomogeneous 48 := by
  unfold a13055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha07248.pow 1)))

end CycleQ2Concrete
