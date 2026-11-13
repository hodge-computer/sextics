import Proposal.CurrentAtoms010

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a04608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04606 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a04607 ^ 1)
theorem ha04608 : a04608.IsHomogeneous 18 := by
  unfold a04608
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04606.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha04607.pow 1)))

@[irreducible]
def a04609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04605 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04608 ^ 1)
theorem ha04609 : a04609.IsHomogeneous 46 := by
  unfold a04609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04605.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04608.pow 1)))

@[irreducible]
def a04610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04609 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01239 ^ 1)
theorem ha04610 : a04610.IsHomogeneous 46 := by
  unfold a04610
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04609.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01239.pow 1)))

@[irreducible]
def a04611 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04610 ^ 1)
theorem ha04611 : a04611.IsHomogeneous 84 := by
  unfold a04611
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02252.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04610.pow 1)))

@[irreducible]
def a04612 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a04611 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04601 ^ 1)
theorem ha04612 : a04612.IsHomogeneous 84 := by
  unfold a04612
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha04611.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04601.pow 1)))

@[irreducible]
def a04613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00375 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01060 ^ 1)
theorem ha04613 : a04613.IsHomogeneous 92 := by
  unfold a04613
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00375.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a04614 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a02461 ^ 1)
theorem ha04614 : a04614.IsHomogeneous 92 := by
  unfold a04614
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01060.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha02461.pow 1)))

@[irreducible]
def a04615 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04613 ^ 1)
theorem ha04615 : a04615.IsHomogeneous 92 := by
  unfold a04615
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04613.pow 1)))

@[irreducible]
def a04616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04615 ^ 1) + (C ((576 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04612 ^ 1)
theorem ha04616 : a04616.IsHomogeneous 97 := by
  unfold a04616
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04615.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((576 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04612.pow 1)))

@[irreducible]
def a04617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00139 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00465 ^ 1)
theorem ha04617 : a04617.IsHomogeneous 84 := by
  unfold a04617
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00139.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a04618 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00061 ^ 1 * a01240 ^ 1)
theorem ha04618 : a04618.IsHomogeneous 84 := by
  unfold a04618
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00465.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00061.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a04619 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a04618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04617 ^ 1)
theorem ha04619 : a04619.IsHomogeneous 84 := by
  unfold a04619
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha04618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04617.pow 1)))

@[irreducible]
def a04620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04616 ^ 1) + (C ((288 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04619 ^ 1)
theorem ha04620 : a04620.IsHomogeneous 97 := by
  unfold a04620
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04616.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((288 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04619.pow 1)))

@[irreducible]
def a04621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00042 ^ 1 * a00126 ^ 1 * a00595 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00188 ^ 1 * a00300 ^ 1)
theorem ha04621 : a04621.IsHomogeneous 103 := by
  unfold a04621
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00595.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00188.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a04622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00046 ^ 1 * a00817 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00300 ^ 1)
theorem ha04622 : a04622.IsHomogeneous 97 := by
  unfold a04622
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00046.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a04623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04622 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04621 ^ 1)
theorem ha04623 : a04623.IsHomogeneous 103 := by
  unfold a04623
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04621.pow 1)))

@[irreducible]
def a04624 : Poly := (C ((-3 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04623 ^ 1)
theorem ha04624 : a04624.IsHomogeneous 103 := by
  unfold a04624
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04623.pow 1)))

@[irreducible]
def a04625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02261 ^ 1)
theorem ha04625 : a04625.IsHomogeneous 84 := by
  unfold a04625
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha00963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02261.pow 1)))

@[irreducible]
def a04626 : Poly := (C ((-1 : ℂ) / (729 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04604 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01236 ^ 1)
theorem ha04626 : a04626.IsHomogeneous 46 := by
  unfold a04626
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (729 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04604.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01236.pow 1)))

@[irreducible]
def a04627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04626 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04608 ^ 1)
theorem ha04627 : a04627.IsHomogeneous 46 := by
  unfold a04627
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04626.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04608.pow 1)))

@[irreducible]
def a04628 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04627 ^ 1)
theorem ha04628 : a04628.IsHomogeneous 84 := by
  unfold a04628
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02261.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04627.pow 1)))

@[irreducible]
def a04629 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04628 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04625 ^ 1)
theorem ha04629 : a04629.IsHomogeneous 84 := by
  unfold a04629
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04628.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04625.pow 1)))

@[irreducible]
def a04630 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00379 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01067 ^ 1)
theorem ha04630 : a04630.IsHomogeneous 92 := by
  unfold a04630
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00379.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a04631 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a02474 ^ 1)
theorem ha04631 : a04631.IsHomogeneous 92 := by
  unfold a04631
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01067.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha02474.pow 1)))

@[irreducible]
def a04632 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04630 ^ 1)
theorem ha04632 : a04632.IsHomogeneous 92 := by
  unfold a04632
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04631.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04630.pow 1)))

@[irreducible]
def a04633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04632 ^ 1) + (C ((648 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04629 ^ 1)
theorem ha04633 : a04633.IsHomogeneous 97 := by
  unfold a04633
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((648 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04629.pow 1)))

@[irreducible]
def a04634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00141 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00469 ^ 1)
theorem ha04634 : a04634.IsHomogeneous 84 := by
  unfold a04634
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00141.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a04635 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00061 ^ 1 * a01248 ^ 1)
theorem ha04635 : a04635.IsHomogeneous 84 := by
  unfold a04635
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00469.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00061.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a04636 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a04635 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04634 ^ 1)
theorem ha04636 : a04636.IsHomogeneous 84 := by
  unfold a04636
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha04635.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04634.pow 1)))

@[irreducible]
def a04637 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04633 ^ 1) + (C ((432 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04636 ^ 1)
theorem ha04637 : a04637.IsHomogeneous 97 := by
  unfold a04637
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04633.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04636.pow 1)))

@[irreducible]
def a04638 : Poly := (C ((-1 : ℂ) / (96 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04623 ^ 1)
theorem ha04638 : a04638.IsHomogeneous 103 := by
  unfold a04638
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04637.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04623.pow 1)))

@[irreducible]
def a04639 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a04638 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04624 ^ 1)
theorem ha04639 : a04639.IsHomogeneous 103 := by
  unfold a04639
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha04638.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04624.pow 1)))

@[irreducible]
def a04640 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04604 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01236 ^ 1)
theorem ha04640 : a04640.IsHomogeneous 46 := by
  unfold a04640
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04604.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01236.pow 1)))

@[irreducible]
def a04641 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04640 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04608 ^ 1)
theorem ha04641 : a04641.IsHomogeneous 46 := by
  unfold a04641
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04640.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04608.pow 1)))

@[irreducible]
def a04642 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04641 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01239 ^ 1)
theorem ha04642 : a04642.IsHomogeneous 46 := by
  unfold a04642
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04641.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01239.pow 1)))

@[irreducible]
def a04643 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04642 ^ 1)
theorem ha04643 : a04643.IsHomogeneous 84 := by
  unfold a04643
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02271.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04642.pow 1)))

@[irreducible]
def a04644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02271 ^ 1)
theorem ha04644 : a04644.IsHomogeneous 84 := by
  unfold a04644
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha00970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02271.pow 1)))

@[irreducible]
def a04645 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04644 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04643 ^ 1)
theorem ha04645 : a04645.IsHomogeneous 84 := by
  unfold a04645
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04644.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04643.pow 1)))

@[irreducible]
def a04646 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a02484 ^ 1)
theorem ha04646 : a04646.IsHomogeneous 92 := by
  unfold a04646
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01074.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha02484.pow 1)))

@[irreducible]
def a04647 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00384 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01074 ^ 1)
theorem ha04647 : a04647.IsHomogeneous 92 := by
  unfold a04647
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00384.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a04648 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04647 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04646 ^ 1)
theorem ha04648 : a04648.IsHomogeneous 92 := by
  unfold a04648
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04647.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04646.pow 1)))

@[irreducible]
def a04649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04648 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04645 ^ 1)
theorem ha04649 : a04649.IsHomogeneous 97 := by
  unfold a04649
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04648.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04645.pow 1)))

@[irreducible]
def a04650 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00061 ^ 1 * a01253 ^ 1)
theorem ha04650 : a04650.IsHomogeneous 84 := by
  unfold a04650
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00061.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a04651 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00144 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00473 ^ 1)
theorem ha04651 : a04651.IsHomogeneous 84 := by
  unfold a04651
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00144.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a04652 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a04651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04650 ^ 1)
theorem ha04652 : a04652.IsHomogeneous 84 := by
  unfold a04652
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha04651.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04650.pow 1)))

@[irreducible]
def a04653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04649 ^ 1) + (C ((648 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04652 ^ 1)
theorem ha04653 : a04653.IsHomogeneous 97 := by
  unfold a04653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04649.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((648 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04652.pow 1)))

@[irreducible]
def a04654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04623 ^ 1) + (C ((1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04653 ^ 1)
theorem ha04654 : a04654.IsHomogeneous 103 := by
  unfold a04654
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04623.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04653.pow 1)))

@[irreducible]
def a04655 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a04654 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04639 ^ 1)
theorem ha04655 : a04655.IsHomogeneous 103 := by
  unfold a04655
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha04654.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04639.pow 1)))

@[irreducible]
def a04656 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a02278 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00127 ^ 1 * a04655 ^ 1)
theorem ha04656 : a04656.IsHomogeneous 121 := by
  unfold a04656
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha02278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00127.pow 1)).mul (ha04655.pow 1)))

@[irreducible]
def a04657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04656 ^ 1)
theorem ha04657 : a04657.IsHomogeneous 121 := by
  unfold a04657
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04656.pow 1)))

@[irreducible]
def a04658 : Poly := (C ((-3 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04599 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a04657 ^ 1)
theorem ha04658 : a04658.IsHomogeneous 139 := by
  unfold a04658
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04599.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha04657.pow 1)))

@[irreducible]
def a04659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02280 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04658 ^ 1)
theorem ha04659 : a04659.IsHomogeneous 139 := by
  unfold a04659
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04658.pow 1)))

@[irreducible]
def a04660 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04587 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a04659 ^ 1)
theorem ha04660 : a04660.IsHomogeneous 139 := by
  unfold a04660
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha04659.pow 1)))

@[irreducible]
def a04661 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 4 * a04660 ^ 1) + (C ((27 : ℂ) / (3200 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a04586 ^ 1)
theorem ha04661 : a04661.IsHomogeneous 163 := by
  unfold a04661
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 4)).mul (ha04660.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (3200 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04586.pow 1)))

@[irreducible]
def a04662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04661 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a02282 ^ 1)
theorem ha04662 : a04662.IsHomogeneous 193 := by
  unfold a04662
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04661.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha02282.pow 1)))

@[irreducible]
def a04663 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04662 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04549 ^ 1)
theorem ha04663 : a04663.IsHomogeneous 193 := by
  unfold a04663
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04662.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04549.pow 1)))

@[irreducible]
def a04664 : Poly := (C ((-27 : ℂ) / (1000 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 4 * a04548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04663 ^ 1)
theorem ha04664 : a04664.IsHomogeneous 193 := by
  unfold a04664
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (1000 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 4)).mul (ha04548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04663.pow 1)))

@[irreducible]
def a04665 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00398 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a01103 ^ 1)
theorem ha04665 : a04665.IsHomogeneous 410 := by
  unfold a04665
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00398.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a02540 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a01103 ^ 1)
theorem ha04666 : a04666.IsHomogeneous 434 := by
  unfold a04666
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha02540.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04666 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a04665 ^ 1)
theorem ha04667 : a04667.IsHomogeneous 434 := by
  unfold a04667
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04666.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha04665.pow 1)))

@[irreducible]
def a04668 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a01099 ^ 1)
theorem ha04668 : a04668.IsHomogeneous 386 := by
  unfold a04668
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha01099.pow 1)))

@[irreducible]
def a04669 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00492 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a01290 ^ 1)
theorem ha04669 : a04669.IsHomogeneous 410 := by
  unfold a04669
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00492.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a04670 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a04668 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04669 ^ 1)
theorem ha04670 : a04670.IsHomogeneous 410 := by
  unfold a04670
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha04668.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04669.pow 1)))

@[irreducible]
def a04671 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00506 ^ 1)
theorem ha04671 : a04671.IsHomogeneous 91 := by
  unfold a04671
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00487.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04672 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00155 ^ 1 * a00487 ^ 1)
theorem ha04672 : a04672.IsHomogeneous 127 := by
  unfold a04672
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha01281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00155.pow 1)).mul (ha00487.pow 1)))

@[irreducible]
def a04673 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04671 ^ 1)
theorem ha04673 : a04673.IsHomogeneous 127 := by
  unfold a04673
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04672.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04671.pow 1)))

@[irreducible]
def a04674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a01270 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a04673 ^ 1)
theorem ha04674 : a04674.IsHomogeneous 139 := by
  unfold a04674
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha01270.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04673.pow 1)))

@[irreducible]
def a04675 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00316 ^ 1 * a00395 ^ 1)
theorem ha04675 : a04675.IsHomogeneous 133 := by
  unfold a04675
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha01097.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00316.pow 1)).mul (ha00395.pow 1)))

@[irreducible]
def a04676 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02530 ^ 1)
theorem ha04676 : a04676.IsHomogeneous 139 := by
  unfold a04676
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01097.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02530.pow 1)))

@[irreducible]
def a04677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04676 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 6 * a04675 ^ 1)
theorem ha04677 : a04677.IsHomogeneous 139 := by
  unfold a04677
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04676.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 6)).mul (ha04675.pow 1)))

@[irreducible]
def a04678 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04674 ^ 1) + (C ((25 : ℂ) / (72 : ℂ)) * a04677 ^ 1)
theorem ha04678 : a04678.IsHomogeneous 139 := by
  unfold a04678
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04674.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (72 : ℂ))).mul (ha04677.pow 1)))

@[irreducible]
def a04679 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02302 ^ 1)
theorem ha04679 : a04679.IsHomogeneous 163 := by
  unfold a04679
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00985.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02302.pow 1)))

@[irreducible]
def a04680 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02295 ^ 1)
theorem ha04680 : a04680.IsHomogeneous 135 := by
  unfold a04680
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha00982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a04681 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00595 ^ 1)
theorem ha04681 : a04681.IsHomogeneous 85 := by
  unfold a04681
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a04682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00046 ^ 1 * a00712 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00260 ^ 1)
theorem ha04682 : a04682.IsHomogeneous 85 := by
  unfold a04682
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00046.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04683 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a04682 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04681 ^ 1)
theorem ha04683 : a04683.IsHomogeneous 85 := by
  unfold a04683
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha04682.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04681.pow 1)))

@[irreducible]
def a04684 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00637 ^ 1)
theorem ha04684 : a04684.IsHomogeneous 97 := by
  unfold a04684
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a04685 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a00691 ^ 1)
theorem ha04685 : a04685.IsHomogeneous 97 := by
  unfold a04685
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a04686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04684 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a04685 ^ 1)
theorem ha04686 : a04686.IsHomogeneous 97 := by
  unfold a04686
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04684.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha04685.pow 1)))

@[irreducible]
def a04687 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04686 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04683 ^ 1)
theorem ha04687 : a04687.IsHomogeneous 99 := by
  unfold a04687
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04686.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04683.pow 1)))

@[irreducible]
def a04688 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04686 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04687 ^ 1)
theorem ha04688 : a04688.IsHomogeneous 99 := by
  unfold a04688
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04686.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04687.pow 1)))

@[irreducible]
def a04689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a04683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04688 ^ 1)
theorem ha04689 : a04689.IsHomogeneous 99 := by
  unfold a04689
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha04683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04688.pow 1)))

@[irreducible]
def a04690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04689 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a02295 ^ 1)
theorem ha04690 : a04690.IsHomogeneous 135 := by
  unfold a04690
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04689.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a04691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04680 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a04690 ^ 1)
theorem ha04691 : a04691.IsHomogeneous 135 := by
  unfold a04691
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04680.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha04690.pow 1)))

@[irreducible]
def a04692 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00393 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01092 ^ 1)
theorem ha04692 : a04692.IsHomogeneous 146 := by
  unfold a04692
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00393.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a04693 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02520 ^ 1)
theorem ha04693 : a04693.IsHomogeneous 146 := by
  unfold a04693
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a04694 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a04693 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04692 ^ 1)
theorem ha04694 : a04694.IsHomogeneous 146 := by
  unfold a04694
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha04693.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04692.pow 1)))

@[irreducible]
def a04695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a04691 ^ 1) + (C ((25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04694 ^ 1)
theorem ha04695 : a04695.IsHomogeneous 148 := by
  unfold a04695
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha04691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04694.pow 1)))

@[irreducible]
def a04696 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00100 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00484 ^ 1)
theorem ha04696 : a04696.IsHomogeneous 133 := by
  unfold a04696
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a04697 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01275 ^ 1)
theorem ha04697 : a04697.IsHomogeneous 133 := by
  unfold a04697
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a04698 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a04697 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04696 ^ 1)
theorem ha04698 : a04698.IsHomogeneous 133 := by
  unfold a04698
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha04697.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04696.pow 1)))

@[irreducible]
def a04699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04695 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a04698 ^ 1)
theorem ha04699 : a04699.IsHomogeneous 148 := by
  unfold a04699
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04695.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha04698.pow 1)))

@[irreducible]
def a04700 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00260 ^ 1)
theorem ha04700 : a04700.IsHomogeneous 85 := by
  unfold a04700
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00829 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00260 ^ 1)
theorem ha04701 : a04701.IsHomogeneous 121 := by
  unfold a04701
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00829.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04700 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a04701 ^ 1)
theorem ha04702 : a04702.IsHomogeneous 121 := by
  unfold a04702
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04700.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha04701.pow 1)))

@[irreducible]
def a04703 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a04702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04699 ^ 1)
theorem ha04703 : a04703.IsHomogeneous 148 := by
  unfold a04703
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha04702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04699.pow 1)))

@[irreducible]
def a04704 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a02302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a04703 ^ 1)
theorem ha04704 : a04704.IsHomogeneous 172 := by
  unfold a04704
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha02302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha04703.pow 1)))

@[irreducible]
def a04705 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04679 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04704 ^ 1)
theorem ha04705 : a04705.IsHomogeneous 172 := by
  unfold a04705
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04704.pow 1)))

@[irreducible]
def a04706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04705 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a04678 ^ 1)
theorem ha04706 : a04706.IsHomogeneous 172 := by
  unfold a04706
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04705.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha04678.pow 1)))

@[irreducible]
def a04707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a02304 ^ 1)
theorem ha04707 : a04707.IsHomogeneous 280 := by
  unfold a04707
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha02304.pow 1)))

@[irreducible]
def a04708 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a00986 ^ 1)
theorem ha04708 : a04708.IsHomogeneous 370 := by
  unfold a04708
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha00986.pow 1)))

@[irreducible]
def a04709 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04708 ^ 1)
theorem ha04709 : a04709.IsHomogeneous 370 := by
  unfold a04709
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04708.pow 1)))

@[irreducible]
def a04710 : Poly := (C ((-25 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a04709 ^ 1) + (C ((25 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00042 ^ 1 * a04670 ^ 1)
theorem ha04710 : a04710.IsHomogeneous 436 := by
  unfold a04710
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04667.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha04709.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00042.pow 1)).mul (ha04670.pow 1)))

@[irreducible]
def a04711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04710 ^ 1) + (C ((25 : ℂ) / (27 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00042 ^ 4 * a00100 ^ 4 * a04664 ^ 1)
theorem ha04711 : a04711.IsHomogeneous 436 := by
  unfold a04711
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04710.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (27 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha04664.pow 1)))

@[irreducible]
def a04712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04711 ^ 1)
theorem ha04712 : a04712.IsHomogeneous 436 := by
  unfold a04712
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04711.pow 1)))

@[irreducible]
def a04713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04712 ^ 1)
theorem ha04713 : a04713.IsHomogeneous 436 := by
  unfold a04713
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04712.pow 1)))

@[irreducible]
def a04714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a04713 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a02308 ^ 1)
theorem ha04714 : a04714.IsHomogeneous 862 := by
  unfold a04714
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha04713.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a04715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04714 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a04539 ^ 1)
theorem ha04715 : a04715.IsHomogeneous 1195 := by
  unfold a04715
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04714.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha04539.pow 1)))

@[irreducible]
def a04716 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a00996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02327 ^ 1)
theorem ha04716 : a04716.IsHomogeneous 1063 := by
  unfold a04716
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha00996.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a04717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02326 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a00996 ^ 1)
theorem ha04717 : a04717.IsHomogeneous 304 := by
  unfold a04717
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02326.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha00996.pow 1)))

@[irreducible]
def a04718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a02313 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00812 ^ 1 * a00991 ^ 1)
theorem ha04718 : a04718.IsHomogeneous 63 := by
  unfold a04718
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha02313.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00812.pow 1)).mul (ha00991.pow 1)))

@[irreducible]
def a04719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02413 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01041 ^ 1)
theorem ha04719 : a04719.IsHomogeneous 24 := by
  unfold a04719
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04720 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a00368 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01041 ^ 1)
theorem ha04720 : a04720.IsHomogeneous 24 := by
  unfold a04720
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha00368.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04719 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a04720 ^ 1)
theorem ha04721 : a04721.IsHomogeneous 24 := by
  unfold a04721
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04719.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha04720.pow 1)))

@[irreducible]
def a04722 : Poly := (C ((-1 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a01298 ^ 1)
theorem ha04722 : a04722.IsHomogeneous 54 := by
  unfold a04722
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a04723 : Poly := (C ((-1 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04722 ^ 1)
theorem ha04723 : a04723.IsHomogeneous 54 := by
  unfold a04723
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04722.pow 1)))

@[irreducible]
def a04724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a01298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04723 ^ 1)
theorem ha04724 : a04724.IsHomogeneous 54 := by
  unfold a04724
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha01298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04723.pow 1)))

@[irreducible]
def a04725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a02313 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a04724 ^ 1)
theorem ha04725 : a04725.IsHomogeneous 72 := by
  unfold a04725
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha02313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha04724.pow 1)))

@[irreducible]
def a04726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04718 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04725 ^ 1)
theorem ha04726 : a04726.IsHomogeneous 72 := by
  unfold a04726
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04718.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04725.pow 1)))

@[irreducible]
def a04727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00400 ^ 1 * a01228 ^ 1)
theorem ha04727 : a04727.IsHomogeneous 64 := by
  unfold a04727
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha01107.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a04728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00138 ^ 1 * a02551 ^ 1)
theorem ha04728 : a04728.IsHomogeneous 73 := by
  unfold a04728
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha01107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00138.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a04729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04728 ^ 1)
theorem ha04729 : a04729.IsHomogeneous 73 := by
  unfold a04729
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04728.pow 1)))

@[irreducible]
def a04730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a04726 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a04729 ^ 1)
theorem ha04730 : a04730.IsHomogeneous 84 := by
  unfold a04730
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha04726.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha04729.pow 1)))

@[irreducible]
def a04731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a01052 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a02441 ^ 1)
theorem ha04731 : a04731.IsHomogeneous 59 := by
  unfold a04731
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha01052.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a04732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00494 ^ 1 * a01052 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a01298 ^ 1)
theorem ha04732 : a04732.IsHomogeneous 67 := by
  unfold a04732
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a04733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a04731 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04732 ^ 1)
theorem ha04733 : a04733.IsHomogeneous 67 := by
  unfold a04733
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha04731.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04732.pow 1)))

@[irreducible]
def a04734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04730 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a04733 ^ 1)
theorem ha04734 : a04734.IsHomogeneous 84 := by
  unfold a04734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04730.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha04733.pow 1)))

@[irreducible]
def a04735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02242 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00126 ^ 1 * a04588 ^ 1)
theorem ha04735 : a04735.IsHomogeneous 52 := by
  unfold a04735
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00126.pow 1)).mul (ha04588.pow 1)))

@[irreducible]
def a04736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a00298 ^ 1 * a02242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a00953 ^ 1)
theorem ha04736 : a04736.IsHomogeneous 84 := by
  unfold a04736
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha00953.pow 1)))

@[irreducible]
def a04737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a04735 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04736 ^ 1)
theorem ha04737 : a04737.IsHomogeneous 84 := by
  unfold a04737
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha04735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04736.pow 1)))

@[irreducible]
def a04738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04734 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a04737 ^ 1)
theorem ha04738 : a04738.IsHomogeneous 84 := by
  unfold a04738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04734.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha04737.pow 1)))

@[irreducible]
def a04739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02320 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a04738 ^ 1)
theorem ha04739 : a04739.IsHomogeneous 90 := by
  unfold a04739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02320.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha04738.pow 1)))

@[irreducible]
def a04740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00994 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02320 ^ 1)
theorem ha04740 : a04740.IsHomogeneous 90 := by
  unfold a04740
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00994.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02320.pow 1)))

@[irreducible]
def a04741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04740 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04739 ^ 1)
theorem ha04741 : a04741.IsHomogeneous 96 := by
  unfold a04741
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04740.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04739.pow 1)))

@[irreducible]
def a04742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01118 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a01275 ^ 1)
theorem ha04742 : a04742.IsHomogeneous 302 := by
  unfold a04742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01118.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a04743 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00484 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02574 ^ 1)
theorem ha04743 : a04743.IsHomogeneous 302 := by
  unfold a04743
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00484.pow 1)).mul (ha01118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a04744 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a04743 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04742 ^ 1)
theorem ha04744 : a04744.IsHomogeneous 302 := by
  unfold a04744
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha04743.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04742.pow 1)))

@[irreducible]
def a04745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02520 ^ 1)
theorem ha04745 : a04745.IsHomogeneous 266 := by
  unfold a04745
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha01092.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a04746 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a01313 ^ 1)
theorem ha04746 : a04746.IsHomogeneous 302 := by
  unfold a04746
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a04747 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a04745 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04746 ^ 1)
theorem ha04747 : a04747.IsHomogeneous 302 := by
  unfold a04747
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha04745.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04746.pow 1)))

@[irreducible]
def a04748 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a02295 ^ 1)
theorem ha04748 : a04748.IsHomogeneous 183 := by
  unfold a04748
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04689.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a04749 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a00982 ^ 1)
theorem ha04749 : a04749.IsHomogeneous 249 := by
  unfold a04749
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a04750 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a04748 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04749 ^ 1)
theorem ha04750 : a04750.IsHomogeneous 249 := by
  unfold a04750
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04748.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04749.pow 1)))

@[irreducible]
def a04751 : Poly := (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04747 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04750 ^ 1) + (C ((25 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04744 ^ 1)
theorem ha04751 : a04751.IsHomogeneous 304 := by
  unfold a04751
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04747.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04744.pow 1)))

@[irreducible]
def a04752 : Poly := (C ((-1 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 5 * a04741 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04751 ^ 1)
theorem ha04752 : a04752.IsHomogeneous 304 := by
  unfold a04752
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 5)).mul (ha04741.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04751.pow 1)))

@[irreducible]
def a04753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02326 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a04752 ^ 1)
theorem ha04753 : a04753.IsHomogeneous 304 := by
  unfold a04753
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha04752.pow 1)))

@[irreducible]
def a04754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04753 ^ 1)
theorem ha04754 : a04754.IsHomogeneous 304 := by
  unfold a04754
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04753.pow 1)))

@[irreducible]
def a04755 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a04754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a02327 ^ 1)
theorem ha04755 : a04755.IsHomogeneous 730 := by
  unfold a04755
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha04754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a04756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04755 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04716 ^ 1)
theorem ha04756 : a04756.IsHomogeneous 1063 := by
  unfold a04756
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04755.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04716.pow 1)))

@[irreducible]
def a04757 : Poly := (C ((-45 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a04529 ^ 1) + (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 5 * a04538 ^ 1) + (C ((-20 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 3 * a00042 ^ 5 * a00100 ^ 1 * a04532 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 2 * a04523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a04715 ^ 1) + (C ((1 : ℂ) / (5400 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 6 * a01196 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 2 * a04526 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 1 * a04535 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 5 * a04756 ^ 1)
theorem ha04757 : a04757.IsHomogeneous 1217 := by
  unfold a04757
  exact (((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha04529.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha04538.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 1)).mul (ha04532.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha04523.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha04715.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5400 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 6)).mul (ha01196.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 2)).mul (ha04526.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 1)).mul (ha04535.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha04756.pow 1)))

@[irreducible]
def a04758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02375 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a01026 ^ 1)
theorem ha04758 : a04758.IsHomogeneous 280 := by
  unfold a04758
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a04759 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1)
theorem ha04759 : a04759.IsHomogeneous 12 := by
  unfold a04759
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)))

@[irreducible]
def a04760 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00368 ^ 1)
theorem ha04760 : a04760.IsHomogeneous 12 := by
  unfold a04760
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a04761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02413 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01041 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01041 ^ 1)
theorem ha04761 : a04761.IsHomogeneous 18 := by
  unfold a04761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01041.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01041.pow 1)))

@[irreducible]
def a04762 : Poly := (C ((-45 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a04760 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04761 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a04759 ^ 1)
theorem ha04762 : a04762.IsHomogeneous 18 := by
  unfold a04762
  exact (((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha04760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04761.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha04759.pow 1)))

@[irreducible]
def a04763 : Poly := (C ((-2 : ℂ) / (405 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a02051 ^ 1)
theorem ha04763 : a04763.IsHomogeneous 48 := by
  unfold a04763
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04762.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha02051.pow 1)))

@[irreducible]
def a04764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1)
theorem ha04764 : a04764.IsHomogeneous 18 := by
  unfold a04764
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a04765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00455 ^ 1)
theorem ha04765 : a04765.IsHomogeneous 12 := by
  unfold a04765
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a04766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00455 ^ 1)
theorem ha04766 : a04766.IsHomogeneous 18 := by
  unfold a04766
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04764 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a04766 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a04765 ^ 1)
theorem ha04767 : a04767.IsHomogeneous 18 := by
  unfold a04767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha04766.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha04765.pow 1)))

@[irreducible]
def a04768 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a04767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04762 ^ 1)
theorem ha04768 : a04768.IsHomogeneous 18 := by
  unfold a04768
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha04767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04762.pow 1)))

@[irreducible]
def a04769 : Poly := (C ((-2 : ℂ) / (405 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04763 ^ 1)
theorem ha04769 : a04769.IsHomogeneous 48 := by
  unfold a04769
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04763.pow 1)))

@[irreducible]
def a04770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a02051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04763 ^ 1)
theorem ha04770 : a04770.IsHomogeneous 48 := by
  unfold a04770
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha02051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04763.pow 1)))

@[irreducible]
def a04771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04770 ^ 1)
theorem ha04771 : a04771.IsHomogeneous 48 := by
  unfold a04771
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04770.pow 1)))

@[irreducible]
def a04772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a02055 ^ 1) + (C ((1 : ℂ) / (80 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04767 ^ 1)
theorem ha04772 : a04772.IsHomogeneous 48 := by
  unfold a04772
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha02055.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (80 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04767.pow 1)))

@[irreducible]
def a04773 : Poly := (C ((-1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04772 ^ 1)
theorem ha04773 : a04773.IsHomogeneous 48 := by
  unfold a04773
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04772.pow 1)))

@[irreducible]
def a04774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04769 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a04773 ^ 1)
theorem ha04774 : a04774.IsHomogeneous 48 := by
  unfold a04774
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04769.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha04773.pow 1)))

@[irreducible]
def a04775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04774 ^ 1)
theorem ha04775 : a04775.IsHomogeneous 48 := by
  unfold a04775
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04774.pow 1)))

@[irreducible]
def a04776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01510 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a01363 ^ 1)
theorem ha04776 : a04776.IsHomogeneous 30 := by
  unfold a04776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha01363.pow 1)))

@[irreducible]
def a04777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a01510 ^ 1)
theorem ha04777 : a04777.IsHomogeneous 51 := by
  unfold a04777
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha01518.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha01510.pow 1)))

@[irreducible]
def a04778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04777 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a04776 ^ 1)
theorem ha04778 : a04778.IsHomogeneous 52 := by
  unfold a04778
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04777.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha04776.pow 1)))

@[irreducible]
def a04779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00007 ^ 1 * a01681 ^ 1) + (C ((1 : ℂ) / (864 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01363 ^ 1)
theorem ha04779 : a04779.IsHomogeneous 58 := by
  unfold a04779
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00007.pow 1)).mul (ha01681.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01363.pow 1)))

@[irreducible]
def a04780 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04779 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04776 ^ 1)
theorem ha04780 : a04780.IsHomogeneous 58 := by
  unfold a04780
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04779.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04776.pow 1)))

@[irreducible]
def a04781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04778 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a04780 ^ 1)
theorem ha04781 : a04781.IsHomogeneous 58 := by
  unfold a04781
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04778.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha04780.pow 1)))

@[irreducible]
def a04782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04777 ^ 1)
theorem ha04782 : a04782.IsHomogeneous 51 := by
  unfold a04782
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha01518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04777.pow 1)))

@[irreducible]
def a04783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04782 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04778 ^ 1)
theorem ha04783 : a04783.IsHomogeneous 52 := by
  unfold a04783
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04782.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04778.pow 1)))

@[irreducible]
def a04784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04783 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04781 ^ 1)
theorem ha04784 : a04784.IsHomogeneous 58 := by
  unfold a04784
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04783.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04781.pow 1)))

@[irreducible]
def a04785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01528 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01397 ^ 1)
theorem ha04785 : a04785.IsHomogeneous 52 := by
  unfold a04785
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01528.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01397.pow 1)))

@[irreducible]
def a04786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04785 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01397 ^ 1)
theorem ha04786 : a04786.IsHomogeneous 52 := by
  unfold a04786
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04785.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01397.pow 1)))

@[irreducible]
def a04787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01387 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a01397 ^ 1)
theorem ha04787 : a04787.IsHomogeneous 24 := by
  unfold a04787
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha01397.pow 1)))

@[irreducible]
def a04788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04787 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a01397 ^ 1)
theorem ha04788 : a04788.IsHomogeneous 24 := by
  unfold a04788
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04787.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha01397.pow 1)))

@[irreducible]
def a04789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04785 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04787 ^ 1)
theorem ha04789 : a04789.IsHomogeneous 52 := by
  unfold a04789
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04785.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04787.pow 1)))

@[irreducible]
def a04790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04786 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04789 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04788 ^ 1)
theorem ha04790 : a04790.IsHomogeneous 52 := by
  unfold a04790
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04786.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04789.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04788.pow 1)))

@[irreducible]
def a04791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01540 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01387 ^ 1)
theorem ha04791 : a04791.IsHomogeneous 52 := by
  unfold a04791
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01540.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01387.pow 1)))

@[irreducible]
def a04792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04791 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04787 ^ 1)
theorem ha04792 : a04792.IsHomogeneous 52 := by
  unfold a04792
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04791.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04787.pow 1)))

@[irreducible]
def a04793 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04791 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01387 ^ 1)
theorem ha04793 : a04793.IsHomogeneous 52 := by
  unfold a04793
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04791.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01387.pow 1)))

@[irreducible]
def a04794 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04793 ^ 1) + (C ((1 : ℂ) / (180 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04788 ^ 1)
theorem ha04794 : a04794.IsHomogeneous 52 := by
  unfold a04794
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04793.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (180 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04788.pow 1)))

@[irreducible]
def a04795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04792 ^ 1)
theorem ha04795 : a04795.IsHomogeneous 52 := by
  unfold a04795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04792.pow 1)))

@[irreducible]
def a04796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04790 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04794 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04795 ^ 1)
theorem ha04796 : a04796.IsHomogeneous 52 := by
  unfold a04796
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04790.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04794.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04795.pow 1)))

@[irreducible]
def a04797 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a01335 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00510 ^ 1)
theorem ha04797 : a04797.IsHomogeneous 24 := by
  unfold a04797
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha01335.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a04798 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00156 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00510 ^ 1)
theorem ha04798 : a04798.IsHomogeneous 24 := by
  unfold a04798
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a04799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00632 ^ 1)
theorem ha04799 : a04799.IsHomogeneous 24 := by
  unfold a04799
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a04800 : Poly := (C ((-432 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04797 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04798 ^ 1)
theorem ha04800 : a04800.IsHomogeneous 30 := by
  unfold a04800
  exact (((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04799.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04797.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04798.pow 1)))

@[irreducible]
def a04801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04800 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01420 ^ 1)
theorem ha04801 : a04801.IsHomogeneous 30 := by
  unfold a04801
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04800.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01420.pow 1)))

@[irreducible]
def a04802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04800 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04801 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01420 ^ 1)
theorem ha04802 : a04802.IsHomogeneous 30 := by
  unfold a04802
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04800.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04801.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01420.pow 1)))

@[irreducible]
def a04803 : Poly := (C ((-28 : ℂ) / (15 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a04800 ^ 1)
theorem ha04803 : a04803.IsHomogeneous 43 := by
  unfold a04803
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-28 : ℂ) / (15 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01565.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha04800.pow 1)))

@[irreducible]
def a04804 : Poly := (C ((-56 : ℂ) / (15 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04803 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a04800 ^ 1)
theorem ha04804 : a04804.IsHomogeneous 43 := by
  unfold a04804
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-56 : ℂ) / (15 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04803.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha04800.pow 1)))

@[irreducible]
def a04805 : Poly := (C ((-28 : ℂ) / (45 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a01420 ^ 1)
theorem ha04805 : a04805.IsHomogeneous 43 := by
  unfold a04805
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-28 : ℂ) / (45 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01565.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01420.pow 1)))

@[irreducible]
def a04806 : Poly := (C ((-56 : ℂ) / (45 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01565 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04805 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a01420 ^ 1)
theorem ha04806 : a04806.IsHomogeneous 43 := by
  unfold a04806
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-56 : ℂ) / (45 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01565.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04805.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01420.pow 1)))

@[irreducible]
def a04807 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04804 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a04802 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04806 ^ 1)
theorem ha04807 : a04807.IsHomogeneous 43 := by
  unfold a04807
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04804.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha04802.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04806.pow 1)))

@[irreducible]
def a04808 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04796 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a04775 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 1 * a04807 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a04784 ^ 1)
theorem ha04808 : a04808.IsHomogeneous 58 := by
  unfold a04808
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04796.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha04775.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha04807.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha04784.pow 1)))

@[irreducible]
def a04809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01180 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00445 ^ 1 * a00691 ^ 1)
theorem ha04809 : a04809.IsHomogeneous 242 := by
  unfold a04809
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01180.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00445.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a04810 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02655 ^ 1)
theorem ha04810 : a04810.IsHomogeneous 278 := by
  unfold a04810
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha01180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a04811 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04810 ^ 1)
theorem ha04811 : a04811.IsHomogeneous 278 := by
  unfold a04811
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04810.pow 1)))

@[irreducible]
def a04812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00362 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00931 ^ 1)
theorem ha04812 : a04812.IsHomogeneous 193 := by
  unfold a04812
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a04813 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02104 ^ 1)
theorem ha04813 : a04813.IsHomogeneous 229 := by
  unfold a04813
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a04814 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04813 ^ 1)
theorem ha04814 : a04814.IsHomogeneous 229 := by
  unfold a04814
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04812.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04813.pow 1)))

@[irreducible]
def a04815 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00327 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00134 ^ 1 * a00595 ^ 1)
theorem ha04815 : a04815.IsHomogeneous 145 := by
  unfold a04815
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a04816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00880 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00327 ^ 1)
theorem ha04816 : a04816.IsHomogeneous 181 := by
  unfold a04816
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00880.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a04817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04816 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04815 ^ 1)
theorem ha04817 : a04817.IsHomogeneous 181 := by
  unfold a04817
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04816.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04815.pow 1)))

@[irreducible]
def a04818 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04814 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a04817 ^ 1) + (C ((25 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04811 ^ 1)
theorem ha04818 : a04818.IsHomogeneous 280 := by
  unfold a04818
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04814.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha04817.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04811.pow 1)))

@[irreducible]
def a04819 : Poly := (C ((-1 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 5 * a00100 ^ 5 * a04808 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04818 ^ 1)
theorem ha04819 : a04819.IsHomogeneous 280 := by
  unfold a04819
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 5)).mul (ha00100.pow 5)).mul (ha04808.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04818.pow 1)))

@[irreducible]
def a04820 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02375 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a04819 ^ 1)
theorem ha04820 : a04820.IsHomogeneous 280 := by
  unfold a04820
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02375.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha04819.pow 1)))

@[irreducible]
def a04821 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04758 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04820 ^ 1)
theorem ha04821 : a04821.IsHomogeneous 280 := by
  unfold a04821
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04758.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04820.pow 1)))

@[irreducible]
def a04822 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a04821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a02376 ^ 1)
theorem ha04822 : a04822.IsHomogeneous 838 := by
  unfold a04822
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha04821.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a04823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a01026 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a02376 ^ 1)
theorem ha04823 : a04823.IsHomogeneous 1285 := by
  unfold a04823
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha01026.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a04824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04823 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a04822 ^ 1)
theorem ha04824 : a04824.IsHomogeneous 1285 := by
  unfold a04824
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04823.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha04822.pow 1)))

@[irreducible]
def a04825 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 3 * a04824 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 3 * a04757 ^ 1)
theorem ha04825 : a04825.IsHomogeneous 1397 := by
  unfold a04825
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha04824.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 3)).mul (ha04757.pow 1)))

@[irreducible]
def a04826 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a02655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a01180 ^ 1)
theorem ha04826 : a04826.IsHomogeneous 1371 := by
  unfold a04826
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha02655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a04827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00935 ^ 1 * a01180 ^ 1)
theorem ha04827 : a04827.IsHomogeneous 1788 := by
  unfold a04827
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00935.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a04828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04827 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04826 ^ 1)
theorem ha04828 : a04828.IsHomogeneous 1788 := by
  unfold a04828
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04827.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04826.pow 1)))

@[irreducible]
def a04829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04825 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a04828 ^ 1)
theorem ha04829 : a04829.IsHomogeneous 1850 := by
  unfold a04829
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04825.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha04828.pow 1)))

@[irreducible]
def a04830 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a02115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04249 ^ 1)
theorem ha04830 : a04830.IsHomogeneous 2266 := by
  unfold a04830
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha02115.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04249.pow 1)))

@[irreducible]
def a04831 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a01035 ^ 1)
theorem ha04831 : a04831.IsHomogeneous 1035 := by
  unfold a04831
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a04832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a01034 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a02393 ^ 1)
theorem ha04832 : a04832.IsHomogeneous 837 := by
  unfold a04832
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha01034.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha02393.pow 1)))

@[irreducible]
def a04833 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a01034 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01707 ^ 1)
theorem ha04833 : a04833.IsHomogeneous 662 := by
  unfold a04833
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha01034.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a04834 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a04832 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04833 ^ 1)
theorem ha04834 : a04834.IsHomogeneous 916 := by
  unfold a04834
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha04832.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04833.pow 1)))

@[irreducible]
def a04835 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a01033 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a02391 ^ 1)
theorem ha04835 : a04835.IsHomogeneous 679 := by
  unfold a04835
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha01033.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha02391.pow 1)))

@[irreducible]
def a04836 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00367 ^ 1 * a01871 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a01033 ^ 1)
theorem ha04836 : a04836.IsHomogeneous 933 := by
  unfold a04836
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00367.pow 1)).mul (ha01871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha01033.pow 1)))

@[irreducible]
def a04837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04836 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04835 ^ 1)
theorem ha04837 : a04837.IsHomogeneous 933 := by
  unfold a04837
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04836.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04835.pow 1)))

@[irreducible]
def a04838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00293 ^ 1 * a02384 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00798 ^ 1 * a01029 ^ 1)
theorem ha04838 : a04838.IsHomogeneous 146 := by
  unfold a04838
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00293.pow 1)).mul (ha02384.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00798.pow 1)).mul (ha01029.pow 1)))

@[irreducible]
def a04839 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00798 ^ 1 * a01029 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00365 ^ 1 * a01877 ^ 1)
theorem ha04839 : a04839.IsHomogeneous 146 := by
  unfold a04839
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00798.pow 1)).mul (ha01029.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00365.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a04840 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a04839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04838 ^ 1)
theorem ha04840 : a04840.IsHomogeneous 146 := by
  unfold a04840
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha04839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04838.pow 1)))

@[irreducible]
def a04841 : Poly := (C ((-1 : ℂ) / (48 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a01581 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a01702 ^ 1)
theorem ha04841 : a04841.IsHomogeneous 70 := by
  unfold a04841
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha01581.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha01702.pow 1)))

@[irreducible]
def a04842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a02384 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00125 ^ 1 * a04841 ^ 1)
theorem ha04842 : a04842.IsHomogeneous 145 := by
  unfold a04842
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha02384.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha04841.pow 1)))

@[irreducible]
def a04843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04842 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04838 ^ 1)
theorem ha04843 : a04843.IsHomogeneous 146 := by
  unfold a04843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04838.pow 1)))

@[irreducible]
def a04844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04843 ^ 1)
theorem ha04844 : a04844.IsHomogeneous 146 := by
  unfold a04844
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04840.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04843.pow 1)))

@[irreducible]
def a04845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00261 ^ 1 * a02388 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00713 ^ 1 * a01031 ^ 1)
theorem ha04845 : a04845.IsHomogeneous 145 := by
  unfold a04845
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00261.pow 1)).mul (ha02388.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00713.pow 1)).mul (ha01031.pow 1)))

@[irreducible]
def a04846 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00713 ^ 1 * a01031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00366 ^ 1 * a01703 ^ 1)
theorem ha04846 : a04846.IsHomogeneous 145 := by
  unfold a04846
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00713.pow 1)).mul (ha01031.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00366.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a04847 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a04846 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04845 ^ 1)
theorem ha04847 : a04847.IsHomogeneous 145 := by
  unfold a04847
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha04846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04845.pow 1)))

@[irreducible]
def a04848 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a01678 ^ 1)
theorem ha04848 : a04848.IsHomogeneous 59 := by
  unfold a04848
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a04849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a02388 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00101 ^ 1 * a04848 ^ 1)
theorem ha04849 : a04849.IsHomogeneous 144 := by
  unfold a04849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha02388.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha04848.pow 1)))

@[irreducible]
def a04850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04849 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04845 ^ 1)
theorem ha04850 : a04850.IsHomogeneous 145 := by
  unfold a04850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04849.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04845.pow 1)))

@[irreducible]
def a04851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04850 ^ 1)
theorem ha04851 : a04851.IsHomogeneous 145 := by
  unfold a04851
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04847.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04850.pow 1)))

@[irreducible]
def a04852 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04844 ^ 1) + (C ((5 : ℂ) / (864 : ℂ)) * a00004 ^ 1 * a04851 ^ 1)
theorem ha04852 : a04852.IsHomogeneous 146 := by
  unfold a04852
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04844.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (864 : ℂ))).mul (ha00004.pow 1)).mul (ha04851.pow 1)))

@[irreducible]
def a04853 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a02391 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04852 ^ 1)
theorem ha04853 : a04853.IsHomogeneous 425 := by
  unfold a04853
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha02391.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04852.pow 1)))

@[irreducible]
def a04854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04835 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04853 ^ 1)
theorem ha04854 : a04854.IsHomogeneous 679 := by
  unfold a04854
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04835.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04853.pow 1)))

@[irreducible]
def a04855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04837 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04854 ^ 1)
theorem ha04855 : a04855.IsHomogeneous 933 := by
  unfold a04855
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04837.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04854.pow 1)))

@[irreducible]
def a04856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a02393 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a04855 ^ 1)
theorem ha04856 : a04856.IsHomogeneous 1012 := by
  unfold a04856
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha02393.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha04855.pow 1)))

@[irreducible]
def a04857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04832 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a04856 ^ 1)
theorem ha04857 : a04857.IsHomogeneous 1091 := by
  unfold a04857
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04832.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha04856.pow 1)))

@[irreducible]
def a04858 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a04857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04834 ^ 1)
theorem ha04858 : a04858.IsHomogeneous 1170 := by
  unfold a04858
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha04857.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04834.pow 1)))

@[irreducible]
def a04859 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a02395 ^ 1)
theorem ha04859 : a04859.IsHomogeneous 1278 := by
  unfold a04859
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04858.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha02395.pow 1)))

@[irreducible]
def a04860 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04859 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04831 ^ 1)
theorem ha04860 : a04860.IsHomogeneous 1368 := by
  unfold a04860
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04859.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04831.pow 1)))

@[irreducible]
def a04861 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01949 ^ 1)
theorem ha04861 : a04861.IsHomogeneous 762 := by
  unfold a04861
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a04862 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04861 ^ 1)
theorem ha04862 : a04862.IsHomogeneous 1095 := by
  unfold a04862
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04831.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04861.pow 1)))

@[irreducible]
def a04863 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04862 ^ 1)
theorem ha04863 : a04863.IsHomogeneous 1428 := by
  unfold a04863
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04860.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04862.pow 1)))

end CycleQ2Concrete
