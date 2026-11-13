import Proposal.CurrentAtoms046

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a13824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13823 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13822 ^ 1)
theorem ha13824 : a13824.IsHomogeneous 2309 := by
  unfold a13824
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13823.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13822.pow 1)))

@[irreducible]
def a13825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07808 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a04252 ^ 1)
theorem ha13825 : a13825.IsHomogeneous 2726 := by
  unfold a13825
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07808.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha04252.pow 1)))

@[irreducible]
def a13826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13825 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13823 ^ 1)
theorem ha13826 : a13826.IsHomogeneous 2726 := by
  unfold a13826
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13825.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13823.pow 1)))

@[irreducible]
def a13827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13826 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13824 ^ 1)
theorem ha13827 : a13827.IsHomogeneous 2726 := by
  unfold a13827
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13826.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13824.pow 1)))

@[irreducible]
def a13828 : Poly := (C ((-81 : ℂ) / (200 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a13821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13827 ^ 1)
theorem ha13828 : a13828.IsHomogeneous 3143 := by
  unfold a13828
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (200 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha13821.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13827.pow 1)))

@[irreducible]
def a13829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a09362 ^ 1) + (C ((25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a13828 ^ 1)
theorem ha13829 : a13829.IsHomogeneous 3155 := by
  unfold a13829
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha09362.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha13828.pow 1)))

@[irreducible]
def a13830 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07813 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13829 ^ 1)
theorem ha13830 : a13830.IsHomogeneous 3155 := by
  unfold a13830
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07813.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13829.pow 1)))

@[irreducible]
def a13831 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13830 ^ 1)
theorem ha13831 : a13831.IsHomogeneous 3155 := by
  unfold a13831
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13830.pow 1)))

@[irreducible]
def a13832 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02043 ^ 1 * a02118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a04255 ^ 1)
theorem ha13832 : a13832.IsHomogeneous 2441 := by
  unfold a13832
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02043.pow 1)).mul (ha02118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha04255.pow 1)))

@[irreducible]
def a13833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08806 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13832 ^ 1)
theorem ha13833 : a13833.IsHomogeneous 2798 := by
  unfold a13833
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08806.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13832.pow 1)))

@[irreducible]
def a13834 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13831 ^ 1)
theorem ha13834 : a13834.IsHomogeneous 3155 := by
  unfold a13834
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13831.pow 1)))

@[irreducible]
def a13835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a04256 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02104 ^ 1 * a02118 ^ 1)
theorem ha13835 : a13835.IsHomogeneous 2382 := by
  unfold a13835
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha04256.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02104.pow 1)).mul (ha02118.pow 1)))

@[irreducible]
def a13836 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a04256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07816 ^ 1)
theorem ha13836 : a13836.IsHomogeneous 2799 := by
  unfold a13836
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha04256.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07816.pow 1)))

@[irreducible]
def a13837 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13836 ^ 1)
theorem ha13837 : a13837.IsHomogeneous 2799 := by
  unfold a13837
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13835.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13836.pow 1)))

@[irreducible]
def a13838 : Poly := (C ((-9 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a13834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13837 ^ 1)
theorem ha13838 : a13838.IsHomogeneous 3216 := by
  unfold a13838
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha13834.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13837.pow 1)))

@[irreducible]
def a13839 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a08805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a13838 ^ 1)
theorem ha13839 : a13839.IsHomogeneous 3222 := by
  unfold a13839
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha08805.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha13838.pow 1)))

@[irreducible]
def a13840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13839 ^ 1)
theorem ha13840 : a13840.IsHomogeneous 3222 := by
  unfold a13840
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07819.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13839.pow 1)))

@[irreducible]
def a13841 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a04258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07819 ^ 1)
theorem ha13841 : a13841.IsHomogeneous 2865 := by
  unfold a13841
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha04258.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07819.pow 1)))

@[irreducible]
def a13842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13840 ^ 1)
theorem ha13842 : a13842.IsHomogeneous 3222 := by
  unfold a13842
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13840.pow 1)))

@[irreducible]
def a13843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a07820 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a04258 ^ 1)
theorem ha13843 : a13843.IsHomogeneous 2866 := by
  unfold a13843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha07820.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha04258.pow 1)))

@[irreducible]
def a13844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13843 ^ 1) + (C ((9 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a13842 ^ 1)
theorem ha13844 : a13844.IsHomogeneous 3283 := by
  unfold a13844
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13843.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha13842.pow 1)))

@[irreducible]
def a13845 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a13844 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a08457 ^ 1)
theorem ha13845 : a13845.IsHomogeneous 3288 := by
  unfold a13845
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha13844.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha08457.pow 1)))

@[irreducible]
def a13846 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07822 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13845 ^ 1)
theorem ha13846 : a13846.IsHomogeneous 3288 := by
  unfold a13846
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13845.pow 1)))

@[irreducible]
def a13847 : Poly := (C ((-12 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00100 ^ 2 * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 4 * a04256 ^ 1) + (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 2 * a00002 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a07820 ^ 1) + (C ((-3 : ℂ) / (500 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 2 * a00004 ^ 3 * a00005 ^ 2 * a00012 ^ 3 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 4 * a00101 ^ 4 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 4 * a00124 ^ 4 * a00134 ^ 8 * a00935 ^ 1) + (C ((-3 : ℂ) / (500 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 4 * a00004 ^ 3 * a00005 ^ 3 * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 7 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00123 ^ 5 * a00124 ^ 5 * a00126 ^ 1 * a00134 ^ 10 * a00328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13846 ^ 1) + (C ((1 : ℂ) / (160 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 3 * a00100 ^ 3 * a00101 ^ 3 * a00103 ^ 3 * a00105 ^ 3 * a00123 ^ 3 * a00124 ^ 3 * a00134 ^ 6 * a02116 ^ 1)
theorem ha13847 : a13847.IsHomogeneous 3288 := by
  unfold a13847
  exact (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 4)).mul (ha04256.pow 1)).add (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha07820.pow 1))).add (((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (500 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00004.pow 3)).mul (ha00005.pow 2)).mul (ha00012.pow 3)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha00101.pow 4)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 4)).mul (ha00124.pow 4)).mul (ha00134.pow 8)).mul (ha00935.pow 1))).add (((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (500 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 7)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00126.pow 1)).mul (ha00134.pow 10)).mul (ha00328.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13846.pow 1))).add (((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (160 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha00101.pow 3)).mul (ha00103.pow 3)).mul (ha00105.pow 3)).mul (ha00123.pow 3)).mul (ha00124.pow 3)).mul (ha00134.pow 6)).mul (ha02116.pow 1)))

@[irreducible]
def a13848 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00018 ^ 1 * a00030 ^ 1 * a00130 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00027 ^ 1 * a07962 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00018 ^ 1 * a00034 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00018 ^ 1 * a00031 ^ 1 * a07964 ^ 1)
theorem ha13848 : a13848.IsHomogeneous 63 := by
  unfold a13848
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha00030.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00027.pow 1)).mul (ha07962.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00018.pow 1)).mul (ha00034.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00018.pow 1)).mul (ha00031.pow 1)).mul (ha07964.pow 1)))

@[irreducible]
def a13849 : Poly := (C ((-36 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00100 ^ 2 * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 4 * a02118 ^ 1) + (C ((-9 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 3 * a00100 ^ 3 * a00101 ^ 3 * a00103 ^ 3 * a00105 ^ 3 * a00123 ^ 3 * a00124 ^ 3 * a00134 ^ 6 * a00937 ^ 1) + (C ((-6 : ℂ) / (5 : ℂ)) * a00001 ^ 2 * a00002 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07822 ^ 1) + (C ((9 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 2 * a00004 ^ 3 * a00005 ^ 2 * a00012 ^ 3 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 4 * a00101 ^ 4 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 4 * a00124 ^ 4 * a00126 ^ 1 * a00134 ^ 8 * a00364 ^ 1) + (C ((81 : ℂ) / (250 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 4 * a00004 ^ 3 * a00005 ^ 3 * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 7 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00117 ^ 1 * a00123 ^ 5 * a00124 ^ 5 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a00134 ^ 10)
theorem ha13849 : a13849.IsHomogeneous 2829 := by
  unfold a13849
  exact (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 4)).mul (ha02118.pow 1)).add (((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha00101.pow 3)).mul (ha00103.pow 3)).mul (ha00105.pow 3)).mul (ha00123.pow 3)).mul (ha00124.pow 3)).mul (ha00134.pow 6)).mul (ha00937.pow 1))).add (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04258.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07822.pow 1))).add ((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00004.pow 3)).mul (ha00005.pow 2)).mul (ha00012.pow 3)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha00101.pow 4)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 4)).mul (ha00124.pow 4)).mul (ha00126.pow 1)).mul (ha00134.pow 8)).mul (ha00364.pow 1))).add (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (250 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 7)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00117.pow 1)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00134.pow 10)))

@[irreducible]
def a13850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00033 ^ 1 * a13847 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a13848 ^ 1 * a13849 ^ 1)
theorem ha13850 : a13850.IsHomogeneous 3351 := by
  unfold a13850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00033.pow 1)).mul (ha13847.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha13848.pow 1)).mul (ha13849.pow 1)))

@[irreducible]
def a13851 : Poly := (C ((-486 : ℂ) / (125 : ℂ)) * a00001 ^ 2 * a00014 ^ 2 * a00042 ^ 6 * a00100 ^ 6 * a00101 ^ 6 * a00103 ^ 4 * a00105 ^ 5 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 12 * a08292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00013 ^ 3 * a00018 ^ 2 * a00106 ^ 2 * a00107 ^ 1 * a07867 ^ 2 * a07942 ^ 2 * a07947 ^ 2 * a13850 ^ 1)
theorem ha13851 : a13851.IsHomogeneous 4397 := by
  unfold a13851
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-486 : ℂ) / (125 : ℂ))).mul (ha00001.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha00100.pow 6)).mul (ha00101.pow 6)).mul (ha00103.pow 4)).mul (ha00105.pow 5)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 12)).mul (ha08292.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 3)).mul (ha00018.pow 2)).mul (ha00106.pow 2)).mul (ha00107.pow 1)).mul (ha07867.pow 2)).mul (ha07942.pow 2)).mul (ha07947.pow 2)).mul (ha13850.pow 1)))

@[irreducible]
def a13852 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00018 ^ 1 * a07966 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00026 ^ 1 * a07962 ^ 1)
theorem ha13852 : a13852.IsHomogeneous 76 := by
  unfold a13852
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00018.pow 1)).mul (ha07966.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00026.pow 1)).mul (ha07962.pow 1)))

@[irreducible]
def a13853 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5)
theorem ha13853 : a13853.IsHomogeneous 5 := by
  unfold a13853
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)))

@[irreducible]
def a13854 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00015 ^ 1 * a13852 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00015 ^ 1 * a00026 ^ 1 * a07962 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00026 ^ 1 * a13853 ^ 1)
theorem ha13854 : a13854.IsHomogeneous 83 := by
  unfold a13854
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00015.pow 1)).mul (ha13852.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00015.pow 1)).mul (ha00026.pow 1)).mul (ha07962.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha13853.pow 1)))

@[irreducible]
def a13855 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13854 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00015 ^ 1 * a00018 ^ 1 * a00026 ^ 1)
theorem ha13855 : a13855.IsHomogeneous 89 := by
  unfold a13855
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13854.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00015.pow 1)).mul (ha00018.pow 1)).mul (ha00026.pow 1)))

@[irreducible]
def a13856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00016 ^ 1 * a13855 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 2 * a00018 ^ 1 * a00024 ^ 1 * a00026 ^ 1)
theorem ha13856 : a13856.IsHomogeneous 95 := by
  unfold a13856
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00016.pow 1)).mul (ha13855.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 2)).mul (ha00018.pow 1)).mul (ha00024.pow 1)).mul (ha00026.pow 1)))

@[irreducible]
def a13857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00019 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00018 ^ 1 * a00032 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00019 ^ 1 * a00029 ^ 1)
theorem ha13857 : a13857.IsHomogeneous 40 := by
  unfold a13857
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00019.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00018.pow 1)).mul (ha00032.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00019.pow 1)).mul (ha00029.pow 1)))

@[irreducible]
def a13858 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00025 ^ 1 * a13857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00018 ^ 1 * a00029 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 8 * a00001 ^ 2 * a00003 ^ 4 * a00004 ^ 2 * a00019 ^ 2 * a00032 ^ 1)
theorem ha13858 : a13858.IsHomogeneous 54 := by
  unfold a13858
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00025.pow 1)).mul (ha13857.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00018.pow 1)).mul (ha00029.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 2)).mul (ha00003.pow 4)).mul (ha00004.pow 2)).mul (ha00019.pow 2)).mul (ha00032.pow 1)))

@[irreducible]
def a13859 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00018 ^ 1 * a13858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00026 ^ 1 * a00029 ^ 1)
theorem ha13859 : a13859.IsHomogeneous 78 := by
  unfold a13859
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00018.pow 1)).mul (ha13858.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00026.pow 1)).mul (ha00029.pow 1)))

@[irreducible]
def a13860 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00015 ^ 1 * a13859 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00018 ^ 1 * a00026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00015 ^ 1 * a00026 ^ 1 * a00029 ^ 1)
theorem ha13860 : a13860.IsHomogeneous 84 := by
  unfold a13860
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00015.pow 1)).mul (ha13859.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha00026.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00015.pow 1)).mul (ha00026.pow 1)).mul (ha00029.pow 1)))

@[irreducible]
def a13861 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00018 ^ 1 * a00026 ^ 1 * a07953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00016 ^ 1 * a13860 ^ 1)
theorem ha13861 : a13861.IsHomogeneous 90 := by
  unfold a13861
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha07953.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00016.pow 1)).mul (ha13860.pow 1)))

@[irreducible]
def a13862 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00018 ^ 1 * a00033 ^ 1 * a13856 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07969 ^ 1 * a13861 ^ 1)
theorem ha13862 : a13862.IsHomogeneous 183 := by
  unfold a13862
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha13856.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07969.pow 1)).mul (ha13861.pow 1)))

@[irreducible]
def a13863 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00018 ^ 1 * a07972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00026 ^ 1 * a07970 ^ 1)
theorem ha13863 : a13863.IsHomogeneous 65 := by
  unfold a13863
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00018.pow 1)).mul (ha07972.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00026.pow 1)).mul (ha07970.pow 1)))

@[irreducible]
def a13864 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a13863 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00026 ^ 1 * a07970 ^ 1)
theorem ha13864 : a13864.IsHomogeneous 65 := by
  unfold a13864
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha13863.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00026.pow 1)).mul (ha07970.pow 1)))

@[irreducible]
def a13865 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00015 ^ 1 * a00016 ^ 1 * a13864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00026 ^ 1 * a07831 ^ 1)
theorem ha13865 : a13865.IsHomogeneous 83 := by
  unfold a13865
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00015.pow 1)).mul (ha00016.pow 1)).mul (ha13864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha07831.pow 1)))

@[irreducible]
def a13866 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00033 ^ 1 * a13865 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07974 ^ 1 * a13861 ^ 1)
theorem ha13866 : a13866.IsHomogeneous 170 := by
  unfold a13866
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha13865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07974.pow 1)).mul (ha13861.pow 1)))

@[irreducible]
def a13867 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a07824 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00003 ^ 1 * a00015 ^ 2 * a00034 ^ 1)
theorem ha13867 : a13867.IsHomogeneous 48 := by
  unfold a13867
  exact (((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha07824.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00003.pow 1)).mul (ha00015.pow 2)).mul (ha00034.pow 1)))

@[irreducible]
def a13868 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00018 ^ 1 * a00033 ^ 1 * a07824 ^ 2 * a07954 ^ 1 * a07958 ^ 1 * a13867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00034 ^ 1 * a07959 ^ 1 * a07960 ^ 2)
theorem ha13868 : a13868.IsHomogeneous 457 := by
  unfold a13868
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha07824.pow 2)).mul (ha07954.pow 1)).mul (ha07958.pow 1)).mul (ha13867.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00034.pow 1)).mul (ha07959.pow 1)).mul (ha07960.pow 2)))

@[irreducible]
def a13869 : Poly := (C ((-1 : ℂ) / (48000 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00013 ^ 1 * a00014 ^ 5 * a00018 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 11 * a07948 ^ 1 * a07960 ^ 2 * a13866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00013 ^ 2 * a00018 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a07823 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 2 * a13862 ^ 1) + (C ((1 : ℂ) / (31104000 : ℂ)) * a00001 ^ 8 * a00002 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00034 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a00123 ^ 5 * a00124 ^ 5 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a13861 ^ 1 * a13868 ^ 1)
theorem ha13869 : a13869.IsHomogeneous 3756 := by
  unfold a13869
  exact ((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48000 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 5)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07948.pow 1)).mul (ha07960.pow 2)).mul (ha13866.pow 1)).add ((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00013.pow 2)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha07823.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 2)).mul (ha13862.pow 1))).add (((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (31104000 : ℂ))).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00034.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha13861.pow 1)).mul (ha13868.pow 1)))

@[irreducible]
def a13870 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00000 ^ 2 * a00003 ^ 1 * a00015 ^ 2 * a00034 ^ 1 * a07824 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00015 ^ 3 * a00026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07824 ^ 3)
theorem ha13870 : a13870.IsHomogeneous 72 := by
  unfold a13870
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 2)).mul (ha00003.pow 1)).mul (ha00015.pow 2)).mul (ha00034.pow 1)).mul (ha07824.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00015.pow 3)).mul (ha00026.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07824.pow 3)))

@[irreducible]
def a13871 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a13870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00015 ^ 3 * a00026 ^ 1)
theorem ha13871 : a13871.IsHomogeneous 72 := by
  unfold a13871
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha13870.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00015.pow 3)).mul (ha00026.pow 1)))

@[irreducible]
def a13872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13869 ^ 1) + (C ((1 : ℂ) / (1500 : ℂ)) * a00000 ^ 6 * a00001 ^ 8 * a00002 ^ 2 * a00003 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00013 ^ 1 * a00014 ^ 4 * a00015 ^ 1 * a00016 ^ 1 * a00018 ^ 3 * a00033 ^ 2 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a00123 ^ 5 * a00124 ^ 5 * a00134 ^ 11 * a07824 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07958 ^ 1 * a13871 ^ 1)
theorem ha13872 : a13872.IsHomogeneous 3756 := by
  unfold a13872
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13869.pow 1)).add (((((((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1500 : ℂ))).mul (ha00000.pow 6)).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00003.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00013.pow 1)).mul (ha00014.pow 4)).mul (ha00015.pow 1)).mul (ha00016.pow 1)).mul (ha00018.pow 3)).mul (ha00033.pow 2)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07824.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07958.pow 1)).mul (ha13871.pow 1)))

@[irreducible]
def a13873 : Poly := (C ((-243 : ℂ) / (250 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 8 * a00026 ^ 2 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07949 ^ 1 * a07960 ^ 3 * a07977 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a13872 ^ 1)
theorem ha13873 : a13873.IsHomogeneous 3757 := by
  unfold a13873
  exact ((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-243 : ℂ) / (250 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 8)).mul (ha00026.pow 2)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07949.pow 1)).mul (ha07960.pow 3)).mul (ha07977.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha13872.pow 1)))

end CycleQ2Concrete
