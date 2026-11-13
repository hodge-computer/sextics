import Proposal.CurrentAtoms026

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a08704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08703 ^ 1)
theorem ha08704 : a08704.IsHomogeneous 67 := by
  unfold a08704
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08694.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08703.pow 1)))

@[irreducible]
def a08705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a02313 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00991 ^ 1 * a01228 ^ 1)
theorem ha08705 : a08705.IsHomogeneous 63 := by
  unfold a08705
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha02313.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00991.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a08706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a02313 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00138 ^ 1 * a04724 ^ 1)
theorem ha08706 : a08706.IsHomogeneous 72 := by
  unfold a08706
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha02313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00138.pow 1)).mul (ha04724.pow 1)))

@[irreducible]
def a08707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08706 ^ 1)
theorem ha08707 : a08707.IsHomogeneous 72 := by
  unfold a08707
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08705.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08706.pow 1)))

@[irreducible]
def a08708 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a08707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a08704 ^ 1)
theorem ha08708 : a08708.IsHomogeneous 79 := by
  unfold a08708
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha08707.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha08704.pow 1)))

@[irreducible]
def a08709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01052 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00400 ^ 1 * a02441 ^ 1)
theorem ha08709 : a08709.IsHomogeneous 66 := by
  unfold a08709
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01052.pow 1)).mul (ha01107.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a08710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a01052 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a02551 ^ 1)
theorem ha08710 : a08710.IsHomogeneous 74 := by
  unfold a08710
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha01052.pow 1)).mul (ha01107.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a08711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08710 ^ 1)
theorem ha08711 : a08711.IsHomogeneous 74 := by
  unfold a08711
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08709.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08710.pow 1)))

@[irreducible]
def a08712 : Poly := (C ((-9 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a08711 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08708 ^ 1)
theorem ha08712 : a08712.IsHomogeneous 85 := by
  unfold a08712
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha08711.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08708.pow 1)))

@[irreducible]
def a08713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a02242 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a04588 ^ 1)
theorem ha08713 : a08713.IsHomogeneous 64 := by
  unfold a08713
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha02242.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha04588.pow 1)))

@[irreducible]
def a08714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00494 ^ 1 * a02242 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00953 ^ 1 * a01298 ^ 1)
theorem ha08714 : a08714.IsHomogeneous 72 := by
  unfold a08714
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00953.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a08715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08714 ^ 1)
theorem ha08715 : a08715.IsHomogeneous 72 := by
  unfold a08715
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08713.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08714.pow 1)))

@[irreducible]
def a08716 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00014 ^ 1 * a08715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08712 ^ 1)
theorem ha08716 : a08716.IsHomogeneous 85 := by
  unfold a08716
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha08715.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08712.pow 1)))

@[irreducible]
def a08717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04368 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00126 ^ 1 * a08540 ^ 1)
theorem ha08717 : a08717.IsHomogeneous 45 := by
  unfold a08717
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00126.pow 1)).mul (ha08540.pow 1)))

@[irreducible]
def a08718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a00298 ^ 1 * a04368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a02133 ^ 1)
theorem ha08718 : a08718.IsHomogeneous 79 := by
  unfold a08718
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha04368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a08719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a08717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08718 ^ 1)
theorem ha08719 : a08719.IsHomogeneous 79 := by
  unfold a08719
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha08717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08718.pow 1)))

@[irreducible]
def a08720 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a08719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08716 ^ 1)
theorem ha08720 : a08720.IsHomogeneous 85 := by
  unfold a08720
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08719.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08716.pow 1)))

@[irreducible]
def a08721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04460 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a08720 ^ 1)
theorem ha08721 : a08721.IsHomogeneous 91 := by
  unfold a08721
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04460.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha08720.pow 1)))

@[irreducible]
def a08722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02181 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04460 ^ 1)
theorem ha08722 : a08722.IsHomogeneous 91 := by
  unfold a08722
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02181.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04460.pow 1)))

@[irreducible]
def a08723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08722 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a08721 ^ 1)
theorem ha08723 : a08723.IsHomogeneous 97 := by
  unfold a08723
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha08721.pow 1)))

@[irreducible]
def a08724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02327 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00996 ^ 1 * a01275 ^ 1)
theorem ha08724 : a08724.IsHomogeneous 347 := by
  unfold a08724
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00996.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a08725 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00484 ^ 1 * a02327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04754 ^ 1)
theorem ha08725 : a08725.IsHomogeneous 347 := by
  unfold a08725
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00484.pow 1)).mul (ha02327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04754.pow 1)))

@[irreducible]
def a08726 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a08725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08724 ^ 1)
theorem ha08726 : a08726.IsHomogeneous 347 := by
  unfold a08726
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha08725.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08724.pow 1)))

@[irreducible]
def a08727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01118 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a02520 ^ 1)
theorem ha08727 : a08727.IsHomogeneous 314 := by
  unfold a08727
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01118.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a08728 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01092 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a02574 ^ 1)
theorem ha08728 : a08728.IsHomogeneous 350 := by
  unfold a08728
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01092.pow 1)).mul (ha01118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a08729 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08728 ^ 1)
theorem ha08729 : a08729.IsHomogeneous 350 := by
  unfold a08729
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08728.pow 1)))

@[irreducible]
def a08730 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a04689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a02295 ^ 1)
theorem ha08730 : a08730.IsHomogeneous 262 := by
  unfold a08730
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha04689.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08731 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00982 ^ 1 * a01313 ^ 1)
theorem ha08731 : a08731.IsHomogeneous 298 := by
  unfold a08731
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00982.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a08732 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a08730 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08731 ^ 1)
theorem ha08732 : a08732.IsHomogeneous 298 := by
  unfold a08732
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha08730.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08731.pow 1)))

@[irreducible]
def a08733 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08661 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a04430 ^ 1)
theorem ha08733 : a08733.IsHomogeneous 181 := by
  unfold a08733
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08661.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha04430.pow 1)))

@[irreducible]
def a08734 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a04430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a02166 ^ 1)
theorem ha08734 : a08734.IsHomogeneous 247 := by
  unfold a08734
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha04430.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a08735 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a08733 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08734 ^ 1)
theorem ha08735 : a08735.IsHomogeneous 247 := by
  unfold a08735
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08733.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08734.pow 1)))

@[irreducible]
def a08736 : Poly := (C ((-25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a08729 ^ 1) + (C ((-4 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a08732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a08726 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a08735 ^ 1)
theorem ha08736 : a08736.IsHomogeneous 351 := by
  unfold a08736
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha08729.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha08732.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha08726.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha08735.pow 1)))

@[irreducible]
def a08737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08736 ^ 1) + (C ((1 : ℂ) / (480 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 4 * a00100 ^ 6 * a08723 ^ 1)
theorem ha08737 : a08737.IsHomogeneous 351 := by
  unfold a08737
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08736.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (480 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 4)).mul (ha00100.pow 6)).mul (ha08723.pow 1)))

@[irreducible]
def a08738 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a08737 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04467 ^ 1)
theorem ha08738 : a08738.IsHomogeneous 351 := by
  unfold a08738
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha08737.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04467.pow 1)))

@[irreducible]
def a08739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08693 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08738 ^ 1)
theorem ha08739 : a08739.IsHomogeneous 351 := by
  unfold a08739
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08693.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08738.pow 1)))

@[irreducible]
def a08740 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a08739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a04468 ^ 1)
theorem ha08740 : a08740.IsHomogeneous 777 := by
  unfold a08740
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha08739.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha04468.pow 1)))

@[irreducible]
def a08741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08740 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08692 ^ 1)
theorem ha08741 : a08741.IsHomogeneous 1110 := by
  unfold a08741
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08692.pow 1)))

@[irreducible]
def a08742 : Poly := (C ((-64 : ℂ) / (9 : ℂ)) * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 6 * a08741 ^ 1) + (C ((-18 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 2 * a08478 ^ 1) + (C ((-8 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 4 * a00042 ^ 6 * a00100 ^ 2 * a08481 ^ 1) + (C ((-5 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 6 * a00100 ^ 1 * a08487 ^ 1) + (C ((-2 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 6 * a08493 ^ 1) + (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 5 * a00042 ^ 4 * a00100 ^ 3 * a08475 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 1 * a08490 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a08484 ^ 1) + (C ((8 : ℂ) / (1125 : ℂ)) * a00000 ^ 1 * a00001 ^ 11 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 5 * a00042 ^ 6 * a00100 ^ 7 * a02395 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00012 ^ 4 * a08691 ^ 1)
theorem ha08742 : a08742.IsHomogeneous 1290 := by
  unfold a08742
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-64 : ℂ) / (9 : ℂ))).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha08741.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha08478.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 6)).mul (ha00100.pow 2)).mul (ha08481.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 6)).mul (ha00100.pow 1)).mul (ha08487.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha08493.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 5)).mul (ha00042.pow 4)).mul (ha00100.pow 3)).mul (ha08475.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 1)).mul (ha08490.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha08484.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 11)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 5)).mul (ha00042.pow 6)).mul (ha00100.pow 7)).mul (ha02395.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00012.pow 4)).mul (ha08691.pow 1)))

@[irreducible]
def a08743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04498 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02203 ^ 1)
theorem ha08743 : a08743.IsHomogeneous 327 := by
  unfold a08743
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04498.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02203.pow 1)))

@[irreducible]
def a08744 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00368 ^ 1) + (C ((-3 : ℂ) / (2 : ℂ)) * a00368 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01041 ^ 1)
theorem ha08744 : a08744.IsHomogeneous 18 := by
  unfold a08744
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00368.pow 1)).mul (ha00506.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a08745 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00368 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00368 ^ 1)
theorem ha08745 : a08745.IsHomogeneous 12 := by
  unfold a08745
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a08746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02413 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01041 ^ 1)
theorem ha08746 : a08746.IsHomogeneous 18 := by
  unfold a08746
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02413.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a08747 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a08745 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08746 ^ 1)
theorem ha08747 : a08747.IsHomogeneous 18 := by
  unfold a08747
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha08745.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08744.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08746.pow 1)))

@[irreducible]
def a08748 : Poly := (C ((-1 : ℂ) / (405 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a08747 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a02586 ^ 1)
theorem ha08748 : a08748.IsHomogeneous 37 := by
  unfold a08748
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (405 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08747.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02586.pow 1)))

@[irreducible]
def a08749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00042 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1)
theorem ha08749 : a08749.IsHomogeneous 30 := by
  unfold a08749
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a08750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00156 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00317 ^ 1)
theorem ha08750 : a08750.IsHomogeneous 27 := by
  unfold a08750
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a08751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00511 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1)
theorem ha08751 : a08751.IsHomogeneous 36 := by
  unfold a08751
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00511.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08751 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08749 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08750 ^ 1)
theorem ha08752 : a08752.IsHomogeneous 36 := by
  unfold a08752
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08751.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08749.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08750.pow 1)))

@[irreducible]
def a08753 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02586 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a08752 ^ 1)
theorem ha08753 : a08753.IsHomogeneous 43 := by
  unfold a08753
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02586.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha08752.pow 1)))

@[irreducible]
def a08754 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a08748 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08753 ^ 1)
theorem ha08754 : a08754.IsHomogeneous 43 := by
  unfold a08754
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08753.pow 1)))

@[irreducible]
def a08755 : Poly := (C ((-1 : ℂ) / (1215 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a08747 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a02586 ^ 1)
theorem ha08755 : a08755.IsHomogeneous 37 := by
  unfold a08755
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08747.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02586.pow 1)))

@[irreducible]
def a08756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08748 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a08755 ^ 1)
theorem ha08756 : a08756.IsHomogeneous 37 := by
  unfold a08756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha08755.pow 1)))

@[irreducible]
def a08757 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a08756 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08754 ^ 1)
theorem ha08757 : a08757.IsHomogeneous 43 := by
  unfold a08757
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08754.pow 1)))

@[irreducible]
def a08758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01436 ^ 1) + (C ((1 : ℂ) / (2430 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01442 ^ 1)
theorem ha08758 : a08758.IsHomogeneous 45 := by
  unfold a08758
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01436.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2430 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01442.pow 1)))

@[irreducible]
def a08759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01436 ^ 1) + (C ((1 : ℂ) / (7290 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01442 ^ 1)
theorem ha08759 : a08759.IsHomogeneous 45 := by
  unfold a08759
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01436.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7290 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01442.pow 1)))

@[irreducible]
def a08760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08758 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a08759 ^ 1)
theorem ha08760 : a08760.IsHomogeneous 45 := by
  unfold a08760
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08758.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha08759.pow 1)))

@[irreducible]
def a08761 : Poly := (C ((-5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a01436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a01482 ^ 1)
theorem ha08761 : a08761.IsHomogeneous 45 := by
  unfold a08761
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha01436.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha01482.pow 1)))

@[irreducible]
def a08762 : Poly := (C ((-5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a08758 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08761 ^ 1)
theorem ha08762 : a08762.IsHomogeneous 51 := by
  unfold a08762
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08758.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08761.pow 1)))

@[irreducible]
def a08763 : Poly := (C ((-5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a08760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08762 ^ 1)
theorem ha08763 : a08763.IsHomogeneous 51 := by
  unfold a08763
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08762.pow 1)))

@[irreducible]
def a08764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01347 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01489 ^ 1)
theorem ha08764 : a08764.IsHomogeneous 39 := by
  unfold a08764
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01347.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01489.pow 1)))

@[irreducible]
def a08765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08764 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01489 ^ 1)
theorem ha08765 : a08765.IsHomogeneous 39 := by
  unfold a08765
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08764.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01489.pow 1)))

@[irreducible]
def a08766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08765 ^ 1)
theorem ha08766 : a08766.IsHomogeneous 39 := by
  unfold a08766
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08765.pow 1)))

@[irreducible]
def a08767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a01335 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00171 ^ 1 * a00510 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1 * a00510 ^ 1)
theorem ha08767 : a08767.IsHomogeneous 42 := by
  unfold a08767
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00171.pow 1)).mul (ha00510.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a08768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00171 ^ 1 * a00510 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00156 ^ 1 * a00555 ^ 1)
theorem ha08768 : a08768.IsHomogeneous 45 := by
  unfold a08768
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00171.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00171.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a08769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00156 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00129 ^ 1 * a00510 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00156 ^ 1 * a00171 ^ 1)
theorem ha08769 : a08769.IsHomogeneous 39 := by
  unfold a08769
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a08770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08768 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a08769 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a08767 ^ 1)
theorem ha08770 : a08770.IsHomogeneous 45 := by
  unfold a08770
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha08769.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha08767.pow 1)))

@[irreducible]
def a08771 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00156 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00155 ^ 1 * a00510 ^ 1)
theorem ha08771 : a08771.IsHomogeneous 30 := by
  unfold a08771
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00155.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a08772 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1 * a00510 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a01335 ^ 1)
theorem ha08772 : a08772.IsHomogeneous 24 := by
  unfold a08772
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a08773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00632 ^ 1)
theorem ha08773 : a08773.IsHomogeneous 24 := by
  unfold a08773
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a08774 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08773 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08771 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a08772 ^ 1)
theorem ha08774 : a08774.IsHomogeneous 30 := by
  unfold a08774
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08773.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08771.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha08772.pow 1)))

@[irreducible]
def a08775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08770 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08774 ^ 1) + (C ((1 : ℂ) / (5832 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a01500 ^ 1)
theorem ha08775 : a08775.IsHomogeneous 45 := by
  unfold a08775
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08770.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08774.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5832 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha01500.pow 1)))

@[irreducible]
def a08776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08775 ^ 1) + (C ((1 : ℂ) / (486 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08774 ^ 1) + (C ((1 : ℂ) / (2916 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a01500 ^ 1)
theorem ha08776 : a08776.IsHomogeneous 45 := by
  unfold a08776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08775.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08774.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2916 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha01500.pow 1)))

@[irreducible]
def a08777 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a08776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08763 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08757 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 1 * a08766 ^ 1)
theorem ha08777 : a08777.IsHomogeneous 51 := by
  unfold a08777
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha08776.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08763.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08757.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha08766.pow 1)))

@[irreducible]
def a08778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02376 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a01026 ^ 1)
theorem ha08778 : a08778.IsHomogeneous 287 := by
  unfold a08778
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02376.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a08779 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a02376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04821 ^ 1)
theorem ha08779 : a08779.IsHomogeneous 323 := by
  unfold a08779
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha02376.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04821.pow 1)))

@[irreducible]
def a08780 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08778 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08779 ^ 1)
theorem ha08780 : a08780.IsHomogeneous 323 := by
  unfold a08780
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08778.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08779.pow 1)))

@[irreducible]
def a08781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00445 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a01180 ^ 1)
theorem ha08781 : a08781.IsHomogeneous 241 := by
  unfold a08781
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00445.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a08782 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02655 ^ 1)
theorem ha08782 : a08782.IsHomogeneous 277 := by
  unfold a08782
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha01180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a08783 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08781 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08782 ^ 1)
theorem ha08783 : a08783.IsHomogeneous 277 := by
  unfold a08783
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08781.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08782.pow 1)))

@[irreducible]
def a08784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00931 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00362 ^ 1 * a00595 ^ 1)
theorem ha08784 : a08784.IsHomogeneous 188 := by
  unfold a08784
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00931.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a08785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a02104 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00931 ^ 1)
theorem ha08785 : a08785.IsHomogeneous 224 := by
  unfold a08785
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha02104.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a08786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08785 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08784 ^ 1)
theorem ha08786 : a08786.IsHomogeneous 224 := by
  unfold a08786
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08785.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08784.pow 1)))

@[irreducible]
def a08787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00173 ^ 1 * a00327 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00558 ^ 1)
theorem ha08787 : a08787.IsHomogeneous 133 := by
  unfold a08787
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00173.pow 1)).mul (ha00327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00558.pow 1)))

@[irreducible]
def a08788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00880 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00173 ^ 1 * a00327 ^ 1)
theorem ha08788 : a08788.IsHomogeneous 169 := by
  unfold a08788
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00880.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00173.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a08789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08788 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08787 ^ 1)
theorem ha08789 : a08789.IsHomogeneous 169 := by
  unfold a08789
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08788.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08787.pow 1)))

@[irreducible]
def a08790 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a08783 ^ 1) + (C ((-4 : ℂ) / (5 : ℂ)) * a00001 ^ 6 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 6 * a00100 ^ 3 * a08789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 2 * a08786 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a08780 ^ 1)
theorem ha08790 : a08790.IsHomogeneous 327 := by
  unfold a08790
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha08783.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00100.pow 3)).mul (ha08789.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha08786.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha08780.pow 1)))

@[irreducible]
def a08791 : Poly := (C ((-2 : ℂ) / (75 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 7 * a00100 ^ 6 * a08777 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08790 ^ 1)
theorem ha08791 : a08791.IsHomogeneous 327 := by
  unfold a08791
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (75 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 7)).mul (ha00100.pow 6)).mul (ha08777.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08790.pow 1)))

@[irreducible]
def a08792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08791 ^ 1)
theorem ha08792 : a08792.IsHomogeneous 327 := by
  unfold a08792
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08791.pow 1)))

@[irreducible]
def a08793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08792 ^ 1)
theorem ha08793 : a08793.IsHomogeneous 327 := by
  unfold a08793
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08792.pow 1)))

@[irreducible]
def a08794 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a08793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a04499 ^ 1)
theorem ha08794 : a08794.IsHomogeneous 885 := by
  unfold a08794
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha08793.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha04499.pow 1)))

@[irreducible]
def a08795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a02203 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a04499 ^ 1)
theorem ha08795 : a08795.IsHomogeneous 1332 := by
  unfold a08795
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha02203.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha04499.pow 1)))

@[irreducible]
def a08796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08795 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a08794 ^ 1)
theorem ha08796 : a08796.IsHomogeneous 1332 := by
  unfold a08796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08795.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha08794.pow 1)))

@[irreducible]
def a08797 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 4 * a08796 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 3 * a08742 ^ 1)
theorem ha08797 : a08797.IsHomogeneous 1470 := by
  unfold a08797
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha08796.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 3)).mul (ha08742.pow 1)))

@[irreducible]
def a08798 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a04821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a02376 ^ 1)
theorem ha08798 : a08798.IsHomogeneous 1416 := by
  unfold a08798
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha04821.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a08799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01026 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00935 ^ 1 * a02376 ^ 1)
theorem ha08799 : a08799.IsHomogeneous 1833 := by
  unfold a08799
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01026.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00935.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a08800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08799 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a08798 ^ 1)
theorem ha08800 : a08800.IsHomogeneous 1833 := by
  unfold a08800
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08799.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha08798.pow 1)))

@[irreducible]
def a08801 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a08797 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 3 * a08800 ^ 1)
theorem ha08801 : a08801.IsHomogeneous 1923 := by
  unfold a08801
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha08797.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 3)).mul (ha08800.pow 1)))

@[irreducible]
def a08802 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00937 ^ 1 * a02655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01180 ^ 1 * a02116 ^ 1)
theorem ha08802 : a08802.IsHomogeneous 1898 := by
  unfold a08802
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00937.pow 1)).mul (ha02655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01180.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a08803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a04252 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a01180 ^ 1 * a02116 ^ 1)
theorem ha08803 : a08803.IsHomogeneous 2315 := by
  unfold a08803
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha04252.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha01180.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a08804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08803 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a08802 ^ 1)
theorem ha08804 : a08804.IsHomogeneous 2315 := by
  unfold a08804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08803.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha08802.pow 1)))

@[irreducible]
def a08805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a08801 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a08804 ^ 1)
theorem ha08805 : a08805.IsHomogeneous 2376 := by
  unfold a08805
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha08801.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha08804.pow 1)))

@[irreducible]
def a08806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07813 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a04255 ^ 1)
theorem ha08806 : a08806.IsHomogeneous 2798 := by
  unfold a08806
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07813.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha04255.pow 1)))

@[irreducible]
def a08807 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a04520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a02213 ^ 1)
theorem ha08807 : a08807.IsHomogeneous 1047 := by
  unfold a08807
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha04520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a08808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a02212 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a04518 ^ 1)
theorem ha08808 : a08808.IsHomogeneous 849 := by
  unfold a08808
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha02212.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha04518.pow 1)))

@[irreducible]
def a08809 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a02212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01707 ^ 1)
theorem ha08809 : a08809.IsHomogeneous 674 := by
  unfold a08809
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha02212.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a08810 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a08808 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08809 ^ 1)
theorem ha08810 : a08810.IsHomogeneous 928 := by
  unfold a08810
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha08808.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08809.pow 1)))

@[irreducible]
def a08811 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a04516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a02211 ^ 1)
theorem ha08811 : a08811.IsHomogeneous 691 := by
  unfold a08811
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha04516.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha02211.pow 1)))

@[irreducible]
def a08812 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a02211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00940 ^ 1 * a01871 ^ 1)
theorem ha08812 : a08812.IsHomogeneous 945 := by
  unfold a08812
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha02211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00940.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a08813 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08812 ^ 1)
theorem ha08813 : a08813.IsHomogeneous 945 := by
  unfold a08813
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08811.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08812.pow 1)))

@[irreducible]
def a08814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a04509 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00798 ^ 1 * a02207 ^ 1)
theorem ha08814 : a08814.IsHomogeneous 153 := by
  unfold a08814
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha04509.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00798.pow 1)).mul (ha02207.pow 1)))

@[irreducible]
def a08815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00938 ^ 1 * a01877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00798 ^ 1 * a02207 ^ 1)
theorem ha08815 : a08815.IsHomogeneous 153 := by
  unfold a08815
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00938.pow 1)).mul (ha01877.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00798.pow 1)).mul (ha02207.pow 1)))

@[irreducible]
def a08816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08814 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08815 ^ 1)
theorem ha08816 : a08816.IsHomogeneous 153 := by
  unfold a08816
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08814.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08815.pow 1)))

@[irreducible]
def a08817 : Poly := (C ((-5 : ℂ) / (4608 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00012 ^ 3 * a00014 ^ 1 * a01507 ^ 1) + (C ((1 : ℂ) / (4608 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 5 * a00005 ^ 3 * a01702 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00012 ^ 2 * a01581 ^ 1)
theorem ha08817 : a08817.IsHomogeneous 77 := by
  unfold a08817
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4608 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha01678.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00012.pow 3)).mul (ha00014.pow 1)).mul (ha01507.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4608 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha01702.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha01581.pow 1)))

@[irreducible]
def a08818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00125 ^ 1 * a08817 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00293 ^ 1 * a04509 ^ 1)
theorem ha08818 : a08818.IsHomogeneous 153 := by
  unfold a08818
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha08817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00293.pow 1)).mul (ha04509.pow 1)))

@[irreducible]
def a08819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08814 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a08818 ^ 1)
theorem ha08819 : a08819.IsHomogeneous 153 := by
  unfold a08819
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08814.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha08818.pow 1)))

@[irreducible]
def a08820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08816 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08819 ^ 1)
theorem ha08820 : a08820.IsHomogeneous 153 := by
  unfold a08820
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08816.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08819.pow 1)))

@[irreducible]
def a08821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00261 ^ 1 * a04513 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00713 ^ 1 * a02209 ^ 1)
theorem ha08821 : a08821.IsHomogeneous 156 := by
  unfold a08821
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00261.pow 1)).mul (ha04513.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00713.pow 1)).mul (ha02209.pow 1)))

@[irreducible]
def a08822 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00713 ^ 1 * a02209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00939 ^ 1 * a01703 ^ 1)
theorem ha08822 : a08822.IsHomogeneous 156 := by
  unfold a08822
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00713.pow 1)).mul (ha02209.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00939.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a08823 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a08822 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08821 ^ 1)
theorem ha08823 : a08823.IsHomogeneous 156 := by
  unfold a08823
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha08822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08821.pow 1)))

@[irreducible]
def a08824 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a01581 ^ 1) + (C ((1 : ℂ) / (80 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a01702 ^ 1)
theorem ha08824 : a08824.IsHomogeneous 70 := by
  unfold a08824
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha01581.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (80 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha01702.pow 1)))

@[irreducible]
def a08825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a04513 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00101 ^ 1 * a08824 ^ 1)
theorem ha08825 : a08825.IsHomogeneous 155 := by
  unfold a08825
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha04513.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha08824.pow 1)))

@[irreducible]
def a08826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a08825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08821 ^ 1)
theorem ha08826 : a08826.IsHomogeneous 156 := by
  unfold a08826
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha08825.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08821.pow 1)))

@[irreducible]
def a08827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08826 ^ 1)
theorem ha08827 : a08827.IsHomogeneous 156 := by
  unfold a08827
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08823.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08826.pow 1)))

@[irreducible]
def a08828 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08820 ^ 1)
theorem ha08828 : a08828.IsHomogeneous 158 := by
  unfold a08828
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08827.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08820.pow 1)))

@[irreducible]
def a08829 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08828 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a04516 ^ 1)
theorem ha08829 : a08829.IsHomogeneous 437 := by
  unfold a08829
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08828.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha04516.pow 1)))

@[irreducible]
def a08830 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08811 ^ 1)
theorem ha08830 : a08830.IsHomogeneous 691 := by
  unfold a08830
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08811.pow 1)))

@[irreducible]
def a08831 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08813 ^ 1)
theorem ha08831 : a08831.IsHomogeneous 945 := by
  unfold a08831
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08830.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08813.pow 1)))

@[irreducible]
def a08832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a04518 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a08831 ^ 1)
theorem ha08832 : a08832.IsHomogeneous 1024 := by
  unfold a08832
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha04518.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha08831.pow 1)))

@[irreducible]
def a08833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08808 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a08832 ^ 1)
theorem ha08833 : a08833.IsHomogeneous 1103 := by
  unfold a08833
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08808.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha08832.pow 1)))

@[irreducible]
def a08834 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a08833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08810 ^ 1)
theorem ha08834 : a08834.IsHomogeneous 1182 := by
  unfold a08834
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha08833.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08810.pow 1)))

@[irreducible]
def a08835 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a04520 ^ 1)
theorem ha08835 : a08835.IsHomogeneous 1290 := by
  unfold a08835
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08834.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha04520.pow 1)))

@[irreducible]
def a08836 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a08835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08807 ^ 1)
theorem ha08836 : a08836.IsHomogeneous 1380 := by
  unfold a08836
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08835.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08807.pow 1)))

@[irreducible]
def a08837 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01949 ^ 1)
theorem ha08837 : a08837.IsHomogeneous 774 := by
  unfold a08837
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a08838 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08807 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08837 ^ 1)
theorem ha08838 : a08838.IsHomogeneous 1107 := by
  unfold a08838
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08807.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08837.pow 1)))

@[irreducible]
def a08839 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08838 ^ 1)
theorem ha08839 : a08839.IsHomogeneous 1440 := by
  unfold a08839
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08836.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08838.pow 1)))

@[irreducible]
def a08840 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a04520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a02213 ^ 1)
theorem ha08840 : a08840.IsHomogeneous 999 := by
  unfold a08840
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha04520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a08841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a04520 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08834 ^ 1)
theorem ha08841 : a08841.IsHomogeneous 1266 := by
  unfold a08841
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha04520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08834.pow 1)))

@[irreducible]
def a08842 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a08841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08840 ^ 1)
theorem ha08842 : a08842.IsHomogeneous 1332 := by
  unfold a08842
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08841.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08840.pow 1)))

@[irreducible]
def a08843 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01979 ^ 1)
theorem ha08843 : a08843.IsHomogeneous 702 := by
  unfold a08843
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a08844 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08843 ^ 1)
theorem ha08844 : a08844.IsHomogeneous 1035 := by
  unfold a08844
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08840.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08843.pow 1)))

@[irreducible]
def a08845 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08842 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08844 ^ 1)
theorem ha08845 : a08845.IsHomogeneous 1368 := by
  unfold a08845
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08842.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08844.pow 1)))

@[irreducible]
def a08846 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01290 ^ 1)
theorem ha08846 : a08846.IsHomogeneous 1120 := by
  unfold a08846
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a08847 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a02395 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a04858 ^ 1)
theorem ha08847 : a08847.IsHomogeneous 1393 := by
  unfold a08847
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha02395.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a08848 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08846 ^ 1)
theorem ha08848 : a08848.IsHomogeneous 1453 := by
  unfold a08848
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08847.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08846.pow 1)))

@[irreducible]
def a08849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02860 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01035 ^ 1 * a01290 ^ 1)
theorem ha08849 : a08849.IsHomogeneous 847 := by
  unfold a08849
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02860.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a08850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08849 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08846 ^ 1)
theorem ha08850 : a08850.IsHomogeneous 1180 := by
  unfold a08850
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08849.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08846.pow 1)))

@[irreducible]
def a08851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08850 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08848 ^ 1)
theorem ha08851 : a08851.IsHomogeneous 1513 := by
  unfold a08851
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08850.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08848.pow 1)))

@[irreducible]
def a08852 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01313 ^ 1)
theorem ha08852 : a08852.IsHomogeneous 1036 := by
  unfold a08852
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a08853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a02395 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a04858 ^ 1)
theorem ha08853 : a08853.IsHomogeneous 1333 := by
  unfold a08853
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha02395.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a08854 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08852 ^ 1)
theorem ha08854 : a08854.IsHomogeneous 1369 := by
  unfold a08854
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08853.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08852.pow 1)))

@[irreducible]
def a08855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02904 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a01035 ^ 1 * a01313 ^ 1)
theorem ha08855 : a08855.IsHomogeneous 739 := by
  unfold a08855
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02904.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a08856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08855 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08852 ^ 1)
theorem ha08856 : a08856.IsHomogeneous 1072 := by
  unfold a08856
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08855.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08852.pow 1)))

@[irreducible]
def a08857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08856 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08854 ^ 1)
theorem ha08857 : a08857.IsHomogeneous 1405 := by
  unfold a08857
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08856.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08854.pow 1)))

@[irreducible]
def a08858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02540 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01103 ^ 1 * a01196 ^ 1)
theorem ha08858 : a08858.IsHomogeneous 1185 := by
  unfold a08858
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02540.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01103.pow 1)).mul (ha01196.pow 1)))

@[irreducible]
def a08859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01103 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02687 ^ 1)
theorem ha08859 : a08859.IsHomogeneous 1458 := by
  unfold a08859
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01103.pow 1)).mul (ha01196.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a08860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08858 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08859 ^ 1)
theorem ha08860 : a08860.IsHomogeneous 1518 := by
  unfold a08860
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08858.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08859.pow 1)))

@[irreducible]
def a08861 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a02540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a05118 ^ 1)
theorem ha08861 : a08861.IsHomogeneous 912 := by
  unfold a08861
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02540.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha05118.pow 1)))

@[irreducible]
def a08862 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08861 ^ 1)
theorem ha08862 : a08862.IsHomogeneous 1245 := by
  unfold a08862
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08858.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08861.pow 1)))

@[irreducible]
def a08863 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08862 ^ 1)
theorem ha08863 : a08863.IsHomogeneous 1578 := by
  unfold a08863
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08860.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08862.pow 1)))

@[irreducible]
def a08864 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a01118 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02574 ^ 1)
theorem ha08864 : a08864.IsHomogeneous 1077 := by
  unfold a08864
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha01118.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a08865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01118 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a02687 ^ 1)
theorem ha08865 : a08865.IsHomogeneous 1374 := by
  unfold a08865
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01118.pow 1)).mul (ha01196.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a08866 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08864 ^ 1)
theorem ha08866 : a08866.IsHomogeneous 1410 := by
  unfold a08866
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08865.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08864.pow 1)))

@[irreducible]
def a08867 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a02574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a05180 ^ 1)
theorem ha08867 : a08867.IsHomogeneous 780 := by
  unfold a08867
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02574.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha05180.pow 1)))

@[irreducible]
def a08868 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08867 ^ 1)
theorem ha08868 : a08868.IsHomogeneous 1113 := by
  unfold a08868
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08864.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08867.pow 1)))

@[irreducible]
def a08869 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a08866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08868 ^ 1)
theorem ha08869 : a08869.IsHomogeneous 1446 := by
  unfold a08869
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha08866.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08868.pow 1)))

@[irreducible]
def a08870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a04713 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a02308 ^ 1)
theorem ha08870 : a08870.IsHomogeneous 1237 := by
  unfold a08870
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha04713.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02308 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00988 ^ 1 * a01886 ^ 1)
theorem ha08871 : a08871.IsHomogeneous 1510 := by
  unfold a08871
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02308.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00988.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a08872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a08870 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a08871 ^ 1)
theorem ha08872 : a08872.IsHomogeneous 1570 := by
  unfold a08872
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha08870.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha08871.pow 1)))

@[irreducible]
def a08873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a04711 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02307 ^ 1)
theorem ha08873 : a08873.IsHomogeneous 502 := by
  unfold a08873
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha04711.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02307.pow 1)))

@[irreducible]
def a08874 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00988 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02307 ^ 1)
theorem ha08874 : a08874.IsHomogeneous 502 := by
  unfold a08874
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00988.pow 1)).mul (ha01946.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02307.pow 1)))

@[irreducible]
def a08875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08873 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08874 ^ 1)
theorem ha08875 : a08875.IsHomogeneous 502 := by
  unfold a08875
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08873.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08874.pow 1)))

@[irreducible]
def a08876 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a01041 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a02413 ^ 1)
theorem ha08876 : a08876.IsHomogeneous 157 := by
  unfold a08876
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).mul (ha01264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a08877 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00148 ^ 1 * a04894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a02413 ^ 1)
theorem ha08877 : a08877.IsHomogeneous 157 := by
  unfold a08877
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha04894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a08878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08877 ^ 1)
theorem ha08878 : a08878.IsHomogeneous 157 := by
  unfold a08878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08876.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08877.pow 1)))

@[irreducible]
def a08879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1 * a01264 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00003 ^ 2 * a00368 ^ 1 * a02814 ^ 1)
theorem ha08879 : a08879.IsHomogeneous 157 := by
  unfold a08879
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)).mul (ha01264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00003.pow 2)).mul (ha00368.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a08880 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a08879 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08876 ^ 1)
theorem ha08880 : a08880.IsHomogeneous 157 := by
  unfold a08880
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha08879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08876.pow 1)))

@[irreducible]
def a08881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08878 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08880 ^ 1)
theorem ha08881 : a08881.IsHomogeneous 157 := by
  unfold a08881
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08880.pow 1)))

@[irreducible]
def a08882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00007 ^ 1 * a00014 ^ 4 * a02715 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a08881 ^ 1)
theorem ha08882 : a08882.IsHomogeneous 169 := by
  unfold a08882
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 4)).mul (ha02715.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08881.pow 1)))

@[irreducible]
def a08883 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01083 ^ 1 * a01207 ^ 1)
theorem ha08883 : a08883.IsHomogeneous 168 := by
  unfold a08883
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02499.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01083.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a08884 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a01083 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00389 ^ 1 * a02710 ^ 1)
theorem ha08884 : a08884.IsHomogeneous 162 := by
  unfold a08884
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha01083.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00389.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a08885 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a08883 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08884 ^ 1)
theorem ha08885 : a08885.IsHomogeneous 168 := by
  unfold a08885
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha08883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08884.pow 1)))

@[irreducible]
def a08886 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00455 ^ 1 * a02499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a05047 ^ 1)
theorem ha08886 : a08886.IsHomogeneous 168 := by
  unfold a08886
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00455.pow 1)).mul (ha02499.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha05047.pow 1)))

@[irreducible]
def a08887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08883 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a08886 ^ 1)
theorem ha08887 : a08887.IsHomogeneous 168 := by
  unfold a08887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha08886.pow 1)))

@[irreducible]
def a08888 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a08887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08885 ^ 1)
theorem ha08888 : a08888.IsHomogeneous 168 := by
  unfold a08888
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha08887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08885.pow 1)))

@[irreducible]
def a08889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08882 ^ 1) + (C ((50 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a08888 ^ 1)
theorem ha08889 : a08889.IsHomogeneous 169 := by
  unfold a08889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08882.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha08888.pow 1)))

@[irreducible]
def a08890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a02282 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00298 ^ 1 * a04661 ^ 1)
theorem ha08890 : a08890.IsHomogeneous 193 := by
  unfold a08890
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha02282.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00298.pow 1)).mul (ha04661.pow 1)))

@[irreducible]
def a08891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a02282 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00976 ^ 1 * a01896 ^ 1)
theorem ha08891 : a08891.IsHomogeneous 184 := by
  unfold a08891
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha02282.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00976.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a08892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08890 ^ 1)
theorem ha08892 : a08892.IsHomogeneous 193 := by
  unfold a08892
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08890.pow 1)))

@[irreducible]
def a08893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a04575 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a00829 ^ 1 * a02236 ^ 1)
theorem ha08893 : a08893.IsHomogeneous 125 := by
  unfold a08893
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04575.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha00829.pow 1)).mul (ha02236.pow 1)))

@[irreducible]
def a08894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00945 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a02227 ^ 1)
theorem ha08894 : a08894.IsHomogeneous 37 := by
  unfold a08894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha02227.pow 1)))

@[irreducible]
def a08895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04557 ^ 1)
theorem ha08895 : a08895.IsHomogeneous 41 := by
  unfold a08895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04557.pow 1)))

@[irreducible]
def a08896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08894 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a08895 ^ 1)
theorem ha08896 : a08896.IsHomogeneous 43 := by
  unfold a08896
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha08895.pow 1)))

@[irreducible]
def a08897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00316 ^ 1)
theorem ha08897 : a08897.IsHomogeneous 12 := by
  unfold a08897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)))

@[irreducible]
def a08898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08897 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00316 ^ 1)
theorem ha08898 : a08898.IsHomogeneous 12 := by
  unfold a08898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08897.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)))

@[irreducible]
def a08899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00506 ^ 1)
theorem ha08899 : a08899.IsHomogeneous 33 := by
  unfold a08899
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a08900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a01327 ^ 1)
theorem ha08900 : a08900.IsHomogeneous 33 := by
  unfold a08900
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a08901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08899 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a08900 ^ 1)
theorem ha08901 : a08901.IsHomogeneous 33 := by
  unfold a08901
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08899.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha08900.pow 1)))

@[irreducible]
def a08902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00865 ^ 1)
theorem ha08902 : a08902.IsHomogeneous 27 := by
  unfold a08902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a08903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08902 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08899 ^ 1)
theorem ha08903 : a08903.IsHomogeneous 33 := by
  unfold a08903
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08899.pow 1)))

@[irreducible]
def a08904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08901 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08903 ^ 1)
theorem ha08904 : a08904.IsHomogeneous 33 := by
  unfold a08904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08903.pow 1)))

@[irreducible]
def a08905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a08898 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a08904 ^ 1)
theorem ha08905 : a08905.IsHomogeneous 38 := by
  unfold a08905
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha08898.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha08904.pow 1)))

@[irreducible]
def a08906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08905 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a08904 ^ 1)
theorem ha08906 : a08906.IsHomogeneous 38 := by
  unfold a08906
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08905.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha08904.pow 1)))

@[irreducible]
def a08907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08905 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08906 ^ 1)
theorem ha08907 : a08907.IsHomogeneous 38 := by
  unfold a08907
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08906.pow 1)))

@[irreducible]
def a08908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08907 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a04557 ^ 1)
theorem ha08908 : a08908.IsHomogeneous 44 := by
  unfold a08908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08907.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha04557.pow 1)))

@[irreducible]
def a08909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08908 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a08895 ^ 1)
theorem ha08909 : a08909.IsHomogeneous 44 := by
  unfold a08909
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08908.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha08895.pow 1)))

@[irreducible]
def a08910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08909 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a08896 ^ 1)
theorem ha08910 : a08910.IsHomogeneous 44 := by
  unfold a08910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08909.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha08896.pow 1)))

@[irreducible]
def a08911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1)
theorem ha08911 : a08911.IsHomogeneous 24 := by
  unfold a08911
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a08912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00506 ^ 1)
theorem ha08912 : a08912.IsHomogeneous 24 := by
  unfold a08912
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a08913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00032 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha08913 : a08913.IsHomogeneous 24 := by
  unfold a08913
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a08914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08913 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a08912 ^ 1)
theorem ha08914 : a08914.IsHomogeneous 24 := by
  unfold a08914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08913.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha08912.pow 1)))

@[irreducible]
def a08915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1)
theorem ha08915 : a08915.IsHomogeneous 18 := by
  unfold a08915
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a08916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha08916 : a08916.IsHomogeneous 12 := by
  unfold a08916
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a08917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08915 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08911 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a08916 ^ 1)
theorem ha08917 : a08917.IsHomogeneous 24 := by
  unfold a08917
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08915.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08911.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha08916.pow 1)))

@[irreducible]
def a08918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1)
theorem ha08918 : a08918.IsHomogeneous 18 := by
  unfold a08918
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a08919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08915 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a08918 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a08912 ^ 1)
theorem ha08919 : a08919.IsHomogeneous 24 := by
  unfold a08919
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08915.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha08918.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha08912.pow 1)))

@[irreducible]
def a08920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08917 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08919 ^ 1)
theorem ha08920 : a08920.IsHomogeneous 24 := by
  unfold a08920
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08917.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08919.pow 1)))

@[irreducible]
def a08921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00130 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1)
theorem ha08921 : a08921.IsHomogeneous 39 := by
  unfold a08921
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a01335 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00510 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a00510 ^ 1)
theorem ha08922 : a08922.IsHomogeneous 36 := by
  unfold a08922
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a08923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00156 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00129 ^ 1 * a00510 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00156 ^ 1)
theorem ha08923 : a08923.IsHomogeneous 39 := by
  unfold a08923
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08921 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a08923 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a08922 ^ 1)
theorem ha08924 : a08924.IsHomogeneous 39 := by
  unfold a08924
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08921.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha08923.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha08922.pow 1)))

@[irreducible]
def a08925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00156 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00129 ^ 1)
theorem ha08925 : a08925.IsHomogeneous 33 := by
  unfold a08925
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a08926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00042 ^ 1)
theorem ha08926 : a08926.IsHomogeneous 30 := by
  unfold a08926
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a08927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08925 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08921 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a08926 ^ 1)
theorem ha08927 : a08927.IsHomogeneous 39 := by
  unfold a08927
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08925.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08921.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha08926.pow 1)))

@[irreducible]
def a08928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha08928 : a08928.IsHomogeneous 33 := by
  unfold a08928
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a08929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08925 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a08928 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a08923 ^ 1)
theorem ha08929 : a08929.IsHomogeneous 39 := by
  unfold a08929
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha08928.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha08923.pow 1)))

@[irreducible]
def a08930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08924 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08929 ^ 1)
theorem ha08930 : a08930.IsHomogeneous 39 := by
  unfold a08930
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08924.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08927.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08929.pow 1)))

@[irreducible]
def a08931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08930 ^ 1) + (C ((1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08920 ^ 1)
theorem ha08931 : a08931.IsHomogeneous 39 := by
  unfold a08931
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08930.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08920.pow 1)))

@[irreducible]
def a08932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08930 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08931 ^ 1) + (C ((1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08920 ^ 1)
theorem ha08932 : a08932.IsHomogeneous 39 := by
  unfold a08932
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08931.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08920.pow 1)))

@[irreducible]
def a08933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08931 ^ 1) + (C ((1 : ℂ) / (5832 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08920 ^ 1)
theorem ha08933 : a08933.IsHomogeneous 39 := by
  unfold a08933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08931.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5832 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08920.pow 1)))

@[irreducible]
def a08934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08932 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08933 ^ 1) + (C ((1 : ℂ) / (3888 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a08920 ^ 1)
theorem ha08934 : a08934.IsHomogeneous 39 := by
  unfold a08934
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08933.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3888 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha08920.pow 1)))

@[irreducible]
def a08935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00176 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (21 : ℂ)) * a00133 ^ 1 * a00570 ^ 1)
theorem ha08935 : a08935.IsHomogeneous 24 := by
  unfold a08935
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00176.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (21 : ℂ))).mul (ha00133.pow 1)).mul (ha00570.pow 1)))

@[irreducible]
def a08936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1)
theorem ha08936 : a08936.IsHomogeneous 18 := by
  unfold a08936
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a08937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08935 ^ 1)
theorem ha08937 : a08937.IsHomogeneous 24 := by
  unfold a08937
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08935.pow 1)))

@[irreducible]
def a08938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a01461 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00570 ^ 1)
theorem ha08938 : a08938.IsHomogeneous 24 := by
  unfold a08938
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha01461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00570.pow 1)))

@[irreducible]
def a08939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08935 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a08938 ^ 1)
theorem ha08939 : a08939.IsHomogeneous 24 := by
  unfold a08939
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha08938.pow 1)))

@[irreducible]
def a08940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08937 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08939 ^ 1)
theorem ha08940 : a08940.IsHomogeneous 24 := by
  unfold a08940
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08937.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08939.pow 1)))

@[irreducible]
def a08941 : Poly := (C ((-9 : ℂ) / (10 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a08934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08910 ^ 1) + (C ((7 : ℂ) / (2160 : ℂ)) * a00000 ^ 13 * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 3 * a08940 ^ 1)
theorem ha08941 : a08941.IsHomogeneous 44 := by
  unfold a08941
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (10 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha08934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08910.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2160 : ℂ))).mul (ha00000.pow 13)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 3)).mul (ha08940.pow 1)))

@[irreducible]
def a08942 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a08941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04575 ^ 1)
theorem ha08942 : a08942.IsHomogeneous 89 := by
  unfold a08942
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha08941.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04575.pow 1)))

@[irreducible]
def a08943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08942 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08893 ^ 1)
theorem ha08943 : a08943.IsHomogeneous 125 := by
  unfold a08943
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08942.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08893.pow 1)))

@[irreducible]
def a08944 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00950 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a02236 ^ 1)
theorem ha08944 : a08944.IsHomogeneous 125 := by
  unfold a08944
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00950.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha02236.pow 1)))

@[irreducible]
def a08945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08893 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a08944 ^ 1)
theorem ha08945 : a08945.IsHomogeneous 125 := by
  unfold a08945
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha08944.pow 1)))

@[irreducible]
def a08946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08945 ^ 1)
theorem ha08946 : a08946.IsHomogeneous 125 := by
  unfold a08946
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08945.pow 1)))

@[irreducible]
def a08947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02432 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01048 ^ 1 * a01275 ^ 1)
theorem ha08947 : a08947.IsHomogeneous 124 := by
  unfold a08947
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01048.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a08948 : Poly := (C ((-27 : ℂ) / (2 : ℂ)) * a00484 ^ 1 * a02432 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a04933 ^ 1)
theorem ha08948 : a08948.IsHomogeneous 124 := by
  unfold a08948
  exact ((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (2 : ℂ))).mul (ha00484.pow 1)).mul (ha02432.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha04933.pow 1)))

@[irreducible]
def a08949 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a08948 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08947 ^ 1)
theorem ha08949 : a08949.IsHomogeneous 124 := by
  unfold a08949
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha08948.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08947.pow 1)))

@[irreducible]
def a08950 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01048 ^ 1 * a01275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a02837 ^ 1)
theorem ha08950 : a08950.IsHomogeneous 125 := by
  unfold a08950
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01048.pow 1)).mul (ha01275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha02837.pow 1)))

@[irreducible]
def a08951 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a08947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08950 ^ 1)
theorem ha08951 : a08951.IsHomogeneous 125 := by
  unfold a08951
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha08947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08950.pow 1)))

@[irreducible]
def a08952 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a08949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08951 ^ 1)
theorem ha08952 : a08952.IsHomogeneous 125 := by
  unfold a08952
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha08949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08951.pow 1)))

@[irreducible]
def a08953 : Poly := (C ((-15 : ℂ) / (1 : ℂ)) * a08952 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08946 ^ 1)
theorem ha08953 : a08953.IsHomogeneous 125 := by
  unfold a08953
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (1 : ℂ))).mul (ha08952.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08946.pow 1)))

@[irreducible]
def a08954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01092 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a02520 ^ 1)
theorem ha08954 : a08954.IsHomogeneous 154 := by
  unfold a08954
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01092.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a08955 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a00393 ^ 1 * a02744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01223 ^ 1)
theorem ha08955 : a08955.IsHomogeneous 148 := by
  unfold a08955
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha00393.pow 1)).mul (ha02744.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01223.pow 1)))

@[irreducible]
def a08956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08955 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08954 ^ 1)
theorem ha08956 : a08956.IsHomogeneous 154 := by
  unfold a08956
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08954.pow 1)))

@[irreducible]
def a08957 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00459 ^ 1 * a02520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a05087 ^ 1)
theorem ha08957 : a08957.IsHomogeneous 161 := by
  unfold a08957
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha02520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha05087.pow 1)))

@[irreducible]
def a08958 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a08954 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08957 ^ 1)
theorem ha08958 : a08958.IsHomogeneous 161 := by
  unfold a08958
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha08954.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08957.pow 1)))

@[irreducible]
def a08959 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a08956 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08958 ^ 1)
theorem ha08959 : a08959.IsHomogeneous 161 := by
  unfold a08959
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha08956.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08958.pow 1)))

end CycleQ2Concrete
