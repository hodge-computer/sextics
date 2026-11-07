import Proposal.CurrentAtoms004

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a02560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a02558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02559 ^ 1)
theorem ha02560 : a02560.IsHomogeneous 79 := by
  unfold a02560
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha02558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02559.pow 1)))

@[irreducible]
def a02561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02557 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02560 ^ 1)
theorem ha02561 : a02561.IsHomogeneous 79 := by
  unfold a02561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02560.pow 1)))

@[irreducible]
def a02562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a02561 ^ 1)
theorem ha02562 : a02562.IsHomogeneous 85 := by
  unfold a02562
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01112.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha02561.pow 1)))

@[irreducible]
def a02563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00402 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01112 ^ 1)
theorem ha02563 : a02563.IsHomogeneous 85 := by
  unfold a02563
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00402.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01112.pow 1)))

@[irreducible]
def a02564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02563 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02562 ^ 1)
theorem ha02564 : a02564.IsHomogeneous 91 := by
  unfold a02564
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02563.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02562.pow 1)))

@[irreducible]
def a02565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a00501 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a01275 ^ 1)
theorem ha02565 : a02565.IsHomogeneous 254 := by
  unfold a02565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha00501.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02566 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00484 ^ 1 * a00501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01313 ^ 1)
theorem ha02566 : a02566.IsHomogeneous 254 := by
  unfold a02566
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00484.pow 1)).mul (ha00501.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a02567 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a02566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02565 ^ 1)
theorem ha02567 : a02567.IsHomogeneous 254 := by
  unfold a02567
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha02566.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02565.pow 1)))

@[irreducible]
def a02568 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02520 ^ 1)
theorem ha02568 : a02568.IsHomogeneous 187 := by
  unfold a02568
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha01092.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a02569 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a00850 ^ 1)
theorem ha02569 : a02569.IsHomogeneous 253 := by
  unfold a02569
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a02570 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a02568 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02569 ^ 1)
theorem ha02570 : a02570.IsHomogeneous 253 := by
  unfold a02570
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02568.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02569.pow 1)))

@[irreducible]
def a02571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02567 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02570 ^ 1)
theorem ha02571 : a02571.IsHomogeneous 259 := by
  unfold a02571
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02567.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02570.pow 1)))

@[irreducible]
def a02572 : Poly := (C ((-1 : ℂ) / (40 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00100 ^ 4 * a02564 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02571 ^ 1)
theorem ha02572 : a02572.IsHomogeneous 259 := by
  unfold a02572
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (40 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00100.pow 4)).mul (ha02564.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02571.pow 1)))

@[irreducible]
def a02573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01117 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02572 ^ 1)
theorem ha02573 : a02573.IsHomogeneous 259 := by
  unfold a02573
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01117.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02572.pow 1)))

@[irreducible]
def a02574 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02544 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02573 ^ 1)
theorem ha02574 : a02574.IsHomogeneous 259 := by
  unfold a02574
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02573.pow 1)))

@[irreducible]
def a02575 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a01118 ^ 1)
theorem ha02575 : a02575.IsHomogeneous 685 := by
  unfold a02575
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02574.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a02576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02543 ^ 1)
theorem ha02576 : a02576.IsHomogeneous 1018 := by
  unfold a02576
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02543.pow 1)))

@[irreducible]
def a02577 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 2 * a00100 ^ 1 * a02398 ^ 1) + (C ((-18 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00042 ^ 1 * a02404 ^ 1) + (C ((-8 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 4 * a02407 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a02542 ^ 1) + (C ((32 : ℂ) / (9 : ℂ)) * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 4 * a02576 ^ 1) + (C ((32 : ℂ) / (9375 : ℂ)) * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 5 * a00804 ^ 1) + (C ((384 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 4 * a00100 ^ 1 * a02401 ^ 1)
theorem ha02577 : a02577.IsHomogeneous 1138 := by
  unfold a02577
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha02398.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00042.pow 1)).mul (ha02404.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02407.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha02542.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02576.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (9375 : ℂ))).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 5)).mul (ha00804.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((384 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 1)).mul (ha02401.pow 1)))

@[irreducible]
def a02578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01179 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a00878 ^ 1)
theorem ha02578 : a02578.IsHomogeneous 235 := by
  unfold a02578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01179.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha00878.pow 1)))

@[irreducible]
def a02579 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01041 ^ 1)
theorem ha02579 : a02579.IsHomogeneous 36 := by
  unfold a02579
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02580 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01041 ^ 1)
theorem ha02580 : a02580.IsHomogeneous 33 := by
  unfold a02580
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02581 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1)
theorem ha02581 : a02581.IsHomogeneous 42 := by
  unfold a02581
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02581 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02580 ^ 1)
theorem ha02582 : a02582.IsHomogeneous 42 := by
  unfold a02582
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02579.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02581.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02580.pow 1)))

@[irreducible]
def a02583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1)
theorem ha02583 : a02583.IsHomogeneous 12 := by
  unfold a02583
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a02584 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 1)
theorem ha02584 : a02584.IsHomogeneous 12 := by
  unfold a02584
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a02585 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00455 ^ 1)
theorem ha02585 : a02585.IsHomogeneous 18 := by
  unfold a02585
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00455.pow 1)))

@[irreducible]
def a02586 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02584 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02583 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02585 ^ 1)
theorem ha02586 : a02586.IsHomogeneous 18 := by
  unfold a02586
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02584.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02583.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02585.pow 1)))

@[irreducible]
def a02587 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02582 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02586 ^ 1)
theorem ha02587 : a02587.IsHomogeneous 49 := by
  unfold a02587
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02582.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02586.pow 1)))

@[irreducible]
def a02588 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02582 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02587 ^ 1)
theorem ha02588 : a02588.IsHomogeneous 49 := by
  unfold a02588
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02587.pow 1)))

@[irreducible]
def a02589 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a00506 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1)
theorem ha02589 : a02589.IsHomogeneous 42 := by
  unfold a02589
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a02590 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha02590 : a02590.IsHomogeneous 36 := by
  unfold a02590
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a02591 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00298 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha02591 : a02591.IsHomogeneous 36 := by
  unfold a02591
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a02592 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02590 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02589 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02591 ^ 1)
theorem ha02592 : a02592.IsHomogeneous 42 := by
  unfold a02592
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02589.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02591.pow 1)))

@[irreducible]
def a02593 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02586 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02592 ^ 1)
theorem ha02593 : a02593.IsHomogeneous 49 := by
  unfold a02593
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02586.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02592.pow 1)))

@[irreducible]
def a02594 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02587 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02593 ^ 1)
theorem ha02594 : a02594.IsHomogeneous 49 := by
  unfold a02594
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02587.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02593.pow 1)))

@[irreducible]
def a02595 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02588 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02594 ^ 1)
theorem ha02595 : a02595.IsHomogeneous 49 := by
  unfold a02595
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02588.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02594.pow 1)))

@[irreducible]
def a02596 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02582 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02588 ^ 1)
theorem ha02596 : a02596.IsHomogeneous 49 := by
  unfold a02596
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02582.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02588.pow 1)))

@[irreducible]
def a02597 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02596 ^ 1)
theorem ha02597 : a02597.IsHomogeneous 49 := by
  unfold a02597
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02595.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02596.pow 1)))

@[irreducible]
def a02598 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02593 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02592 ^ 1)
theorem ha02598 : a02598.IsHomogeneous 49 := by
  unfold a02598
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02593.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02592.pow 1)))

@[irreducible]
def a02599 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02594 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02598 ^ 1)
theorem ha02599 : a02599.IsHomogeneous 49 := by
  unfold a02599
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02594.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02598.pow 1)))

@[irreducible]
def a02600 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02599 ^ 1)
theorem ha02600 : a02600.IsHomogeneous 49 := by
  unfold a02600
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02595.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02599.pow 1)))

@[irreducible]
def a02601 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02597 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02600 ^ 1)
theorem ha02601 : a02601.IsHomogeneous 49 := by
  unfold a02601
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02597.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02600.pow 1)))

@[irreducible]
def a02602 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01436 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01592 ^ 1)
theorem ha02602 : a02602.IsHomogeneous 53 := by
  unfold a02602
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01436.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01592.pow 1)))

@[irreducible]
def a02603 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a01436 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01584 ^ 1)
theorem ha02603 : a02603.IsHomogeneous 50 := by
  unfold a02603
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha01436.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01584.pow 1)))

@[irreducible]
def a02604 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02603 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02602 ^ 1)
theorem ha02604 : a02604.IsHomogeneous 53 := by
  unfold a02604
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02603.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02602.pow 1)))

@[irreducible]
def a02605 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02603 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01584 ^ 1)
theorem ha02605 : a02605.IsHomogeneous 50 := by
  unfold a02605
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02603.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01584.pow 1)))

@[irreducible]
def a02606 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02605 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02604 ^ 1)
theorem ha02606 : a02606.IsHomogeneous 53 := by
  unfold a02606
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02605.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02604.pow 1)))

@[irreducible]
def a02607 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02602 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01592 ^ 1)
theorem ha02607 : a02607.IsHomogeneous 53 := by
  unfold a02607
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02602.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01592.pow 1)))

@[irreducible]
def a02608 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02604 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02607 ^ 1)
theorem ha02608 : a02608.IsHomogeneous 53 := by
  unfold a02608
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02604.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02607.pow 1)))

@[irreducible]
def a02609 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02606 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02608 ^ 1)
theorem ha02609 : a02609.IsHomogeneous 53 := by
  unfold a02609
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02606.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02608.pow 1)))

@[irreducible]
def a02610 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02605 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01584 ^ 1)
theorem ha02610 : a02610.IsHomogeneous 50 := by
  unfold a02610
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02605.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01584.pow 1)))

@[irreducible]
def a02611 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02606 ^ 1)
theorem ha02611 : a02611.IsHomogeneous 53 := by
  unfold a02611
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02610.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02606.pow 1)))

@[irreducible]
def a02612 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02609 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02611 ^ 1)
theorem ha02612 : a02612.IsHomogeneous 53 := by
  unfold a02612
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02609.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02611.pow 1)))

@[irreducible]
def a02613 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01347 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01629 ^ 1)
theorem ha02613 : a02613.IsHomogeneous 53 := by
  unfold a02613
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01347.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01629.pow 1)))

@[irreducible]
def a02614 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02613 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01629 ^ 1)
theorem ha02614 : a02614.IsHomogeneous 53 := by
  unfold a02614
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02613.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01629.pow 1)))

@[irreducible]
def a02615 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02613 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01629 ^ 1)
theorem ha02615 : a02615.IsHomogeneous 53 := by
  unfold a02615
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02613.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01629.pow 1)))

@[irreducible]
def a02616 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02615 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01629 ^ 1)
theorem ha02616 : a02616.IsHomogeneous 53 := by
  unfold a02616
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02615.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01629.pow 1)))

@[irreducible]
def a02617 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01347 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01641 ^ 1)
theorem ha02617 : a02617.IsHomogeneous 53 := by
  unfold a02617
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01347.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01641.pow 1)))

@[irreducible]
def a02618 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02617 ^ 1)
theorem ha02618 : a02618.IsHomogeneous 53 := by
  unfold a02618
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02617.pow 1)))

@[irreducible]
def a02619 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02617 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01641 ^ 1)
theorem ha02619 : a02619.IsHomogeneous 53 := by
  unfold a02619
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02617.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01641.pow 1)))

@[irreducible]
def a02620 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02614 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02619 ^ 1)
theorem ha02620 : a02620.IsHomogeneous 53 := by
  unfold a02620
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02614.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02618.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02619.pow 1)))

@[irreducible]
def a02621 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02618 ^ 1)
theorem ha02621 : a02621.IsHomogeneous 53 := by
  unfold a02621
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02615.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02618.pow 1)))

@[irreducible]
def a02622 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02616 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02621 ^ 1)
theorem ha02622 : a02622.IsHomogeneous 53 := by
  unfold a02622
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02616.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02620.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02621.pow 1)))

@[irreducible]
def a02623 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02617 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01641 ^ 1)
theorem ha02623 : a02623.IsHomogeneous 53 := by
  unfold a02623
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02617.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01641.pow 1)))

@[irreducible]
def a02624 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02618 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02623 ^ 1)
theorem ha02624 : a02624.IsHomogeneous 53 := by
  unfold a02624
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02618.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02623.pow 1)))

@[irreducible]
def a02625 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02619 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02623 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01641 ^ 1)
theorem ha02625 : a02625.IsHomogeneous 53 := by
  unfold a02625
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02619.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02623.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01641.pow 1)))

@[irreducible]
def a02626 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02624 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02625 ^ 1)
theorem ha02626 : a02626.IsHomogeneous 53 := by
  unfold a02626
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02620.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02624.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02625.pow 1)))

@[irreducible]
def a02627 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02624 ^ 1)
theorem ha02627 : a02627.IsHomogeneous 53 := by
  unfold a02627
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02621.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02624.pow 1)))

@[irreducible]
def a02628 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02622 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02626 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02627 ^ 1)
theorem ha02628 : a02628.IsHomogeneous 53 := by
  unfold a02628
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02622.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02626.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02627.pow 1)))

@[irreducible]
def a02629 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1 * a01335 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1 * a00510 ^ 1)
theorem ha02629 : a02629.IsHomogeneous 42 := by
  unfold a02629
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha01335.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a02630 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00156 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00129 ^ 1 * a00510 ^ 1)
theorem ha02630 : a02630.IsHomogeneous 45 := by
  unfold a02630
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a02631 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1 * a00632 ^ 1)
theorem ha02631 : a02631.IsHomogeneous 48 := by
  unfold a02631
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a02632 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a02631 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02630 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a02629 ^ 1)
theorem ha02632 : a02632.IsHomogeneous 48 := by
  unfold a02632
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha02631.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02630.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha02629.pow 1)))

@[irreducible]
def a02633 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01657 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a02632 ^ 1)
theorem ha02633 : a02633.IsHomogeneous 48 := by
  unfold a02633
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01657.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha02632.pow 1)))

@[irreducible]
def a02634 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01657 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02633 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a02632 ^ 1)
theorem ha02634 : a02634.IsHomogeneous 48 := by
  unfold a02634
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01657.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02633.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha02632.pow 1)))

@[irreducible]
def a02635 : Poly := (C ((-1 : ℂ) / (2430 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02632 ^ 1)
theorem ha02635 : a02635.IsHomogeneous 48 := by
  unfold a02635
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2430 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02632.pow 1)))

@[irreducible]
def a02636 : Poly := (C ((-1 : ℂ) / (2430 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02632 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02635 ^ 1)
theorem ha02636 : a02636.IsHomogeneous 48 := by
  unfold a02636
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2430 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02632.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02635.pow 1)))

@[irreducible]
def a02637 : Poly := (C ((-1 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01657 ^ 1)
theorem ha02637 : a02637.IsHomogeneous 48 := by
  unfold a02637
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01657.pow 1)))

@[irreducible]
def a02638 : Poly := (C ((-1 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01657 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02637 ^ 1)
theorem ha02638 : a02638.IsHomogeneous 48 := by
  unfold a02638
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01657.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02637.pow 1)))

@[irreducible]
def a02639 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02634 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02638 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a02636 ^ 1)
theorem ha02639 : a02639.IsHomogeneous 48 := by
  unfold a02639
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02634.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02638.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha02636.pow 1)))

@[irreducible]
def a02640 : Poly := (C ((-1 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02635 ^ 1)
theorem ha02640 : a02640.IsHomogeneous 48 := by
  unfold a02640
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02635.pow 1)))

@[irreducible]
def a02641 : Poly := (C ((-1 : ℂ) / (810 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02636 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02640 ^ 1)
theorem ha02641 : a02641.IsHomogeneous 48 := by
  unfold a02641
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (810 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02636.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02640.pow 1)))

@[irreducible]
def a02642 : Poly := (C ((-2 : ℂ) / (1701 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02637 ^ 1)
theorem ha02642 : a02642.IsHomogeneous 48 := by
  unfold a02642
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1701 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02637.pow 1)))

@[irreducible]
def a02643 : Poly := (C ((-1 : ℂ) / (567 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a01667 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02638 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02642 ^ 1)
theorem ha02643 : a02643.IsHomogeneous 48 := by
  unfold a02643
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (567 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha01667.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02638.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02642.pow 1)))

@[irreducible]
def a02644 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02639 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02643 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a02641 ^ 1)
theorem ha02644 : a02644.IsHomogeneous 48 := by
  unfold a02644
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02639.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02643.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha02641.pow 1)))

@[irreducible]
def a02645 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02628 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a02601 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a02612 ^ 1) + (C ((14 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02644 ^ 1)
theorem ha02645 : a02645.IsHomogeneous 53 := by
  unfold a02645
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02628.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha02601.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha02612.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02644.pow 1)))

@[irreducible]
def a02646 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00931 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00362 ^ 1 * a00691 ^ 1)
theorem ha02646 : a02646.IsHomogeneous 194 := by
  unfold a02646
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00931.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02647 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02104 ^ 1)
theorem ha02647 : a02647.IsHomogeneous 230 := by
  unfold a02647
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a02648 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02646 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02647 ^ 1)
theorem ha02648 : a02648.IsHomogeneous 230 := by
  unfold a02648
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02646.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02647.pow 1)))

@[irreducible]
def a02649 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00134 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00327 ^ 1)
theorem ha02649 : a02649.IsHomogeneous 150 := by
  unfold a02649
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a02650 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00880 ^ 1)
theorem ha02650 : a02650.IsHomogeneous 186 := by
  unfold a02650
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a02651 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a02649 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02650 ^ 1)
theorem ha02651 : a02651.IsHomogeneous 186 := by
  unfold a02651
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha02649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02650.pow 1)))

@[irreducible]
def a02652 : Poly := (C ((-288 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02651 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02648 ^ 1)
theorem ha02652 : a02652.IsHomogeneous 235 := by
  unfold a02652
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-288 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02651.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02648.pow 1)))

@[irreducible]
def a02653 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02652 ^ 1) + (C ((1 : ℂ) / (150 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 4 * a02645 ^ 1)
theorem ha02653 : a02653.IsHomogeneous 235 := by
  unfold a02653
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02652.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (150 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 4)).mul (ha02645.pow 1)))

@[irreducible]
def a02654 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02653 ^ 1)
theorem ha02654 : a02654.IsHomogeneous 235 := by
  unfold a02654
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02653.pow 1)))

@[irreducible]
def a02655 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02578 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02654 ^ 1)
theorem ha02655 : a02655.IsHomogeneous 235 := by
  unfold a02655
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02578.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02654.pow 1)))

@[irreducible]
def a02656 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a02655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a01180 ^ 1)
theorem ha02656 : a02656.IsHomogeneous 793 := by
  unfold a02656
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha02655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a02657 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a00883 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a01180 ^ 1)
theorem ha02657 : a02657.IsHomogeneous 1240 := by
  unfold a02657
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha00883.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a02658 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02657 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a02656 ^ 1)
theorem ha02658 : a02658.IsHomogeneous 1240 := by
  unfold a02658
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02657.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha02656.pow 1)))

@[irreducible]
def a02659 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a02658 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 3 * a02577 ^ 1)
theorem ha02659 : a02659.IsHomogeneous 1318 := by
  unfold a02659
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha02658.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 3)).mul (ha02577.pow 1)))

@[irreducible]
def a02660 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a00934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a02109 ^ 1)
theorem ha02660 : a02660.IsHomogeneous 1739 := by
  unfold a02660
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha00934.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha02109.pow 1)))

@[irreducible]
def a02661 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a00836 ^ 1)
theorem ha02661 : a02661.IsHomogeneous 1028 := by
  unfold a02661
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a02662 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00451 ^ 1 * a00715 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a01194 ^ 1)
theorem ha02662 : a02662.IsHomogeneous 830 := by
  unfold a02662
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00451.pow 1)).mul (ha00715.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01194.pow 1)))

@[irreducible]
def a02663 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00451 ^ 1 * a00715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01707 ^ 1)
theorem ha02663 : a02663.IsHomogeneous 655 := by
  unfold a02663
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00451.pow 1)).mul (ha00715.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a02664 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a02662 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02663 ^ 1)
theorem ha02664 : a02664.IsHomogeneous 909 := by
  unfold a02664
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha02662.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02663.pow 1)))

@[irreducible]
def a02665 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00450 ^ 1 * a00795 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a01192 ^ 1)
theorem ha02665 : a02665.IsHomogeneous 672 := by
  unfold a02665
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00450.pow 1)).mul (ha00795.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha01192.pow 1)))

@[irreducible]
def a02666 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00136 ^ 1 * a01871 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00450 ^ 1 * a00795 ^ 1)
theorem ha02666 : a02666.IsHomogeneous 926 := by
  unfold a02666
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00136.pow 1)).mul (ha01871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00450.pow 1)).mul (ha00795.pow 1)))

@[irreducible]
def a02667 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02666 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02665 ^ 1)
theorem ha02667 : a02667.IsHomogeneous 926 := by
  unfold a02667
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02666.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02665.pow 1)))

@[irreducible]
def a02668 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00293 ^ 1 * a01186 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00447 ^ 1 * a00798 ^ 1)
theorem ha02668 : a02668.IsHomogeneous 135 := by
  unfold a02668
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00293.pow 1)).mul (ha01186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00447.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a02669 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00447 ^ 1 * a00798 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00135 ^ 1 * a01877 ^ 1)
theorem ha02669 : a02669.IsHomogeneous 135 := by
  unfold a02669
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00447.pow 1)).mul (ha00798.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00135.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a02670 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02669 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02668 ^ 1)
theorem ha02670 : a02670.IsHomogeneous 135 := by
  unfold a02670
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02669.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02668.pow 1)))

@[irreducible]
def a02671 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a01678 ^ 1)
theorem ha02671 : a02671.IsHomogeneous 59 := by
  unfold a02671
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a02672 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a01186 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00125 ^ 1 * a02671 ^ 1)
theorem ha02672 : a02672.IsHomogeneous 134 := by
  unfold a02672
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha01186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha02671.pow 1)))

@[irreducible]
def a02673 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a02672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02668 ^ 1)
theorem ha02673 : a02673.IsHomogeneous 135 := by
  unfold a02673
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha02672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02668.pow 1)))

@[irreducible]
def a02674 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02670 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02673 ^ 1)
theorem ha02674 : a02674.IsHomogeneous 135 := by
  unfold a02674
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02670.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02673.pow 1)))

@[irreducible]
def a02675 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00261 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00260 ^ 1 * a00713 ^ 1)
theorem ha02675 : a02675.IsHomogeneous 132 := by
  unfold a02675
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00261.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00260.pow 1)).mul (ha00713.pow 1)))

@[irreducible]
def a02676 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a01702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a00712 ^ 1)
theorem ha02676 : a02676.IsHomogeneous 130 := by
  unfold a02676
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02677 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a02676 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a02675 ^ 1)
theorem ha02677 : a02677.IsHomogeneous 132 := by
  unfold a02677
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha02676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha02675.pow 1)))

@[irreducible]
def a02678 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a00713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a01703 ^ 1)
theorem ha02678 : a02678.IsHomogeneous 132 := by
  unfold a02678
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha00713.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a02679 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02675 ^ 1)
theorem ha02679 : a02679.IsHomogeneous 132 := by
  unfold a02679
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02675.pow 1)))

@[irreducible]
def a02680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02677 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a02679 ^ 1)
theorem ha02680 : a02680.IsHomogeneous 132 := by
  unfold a02680
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02677.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha02679.pow 1)))

@[irreducible]
def a02681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a02674 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a02680 ^ 1)
theorem ha02681 : a02681.IsHomogeneous 139 := by
  unfold a02681
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha02674.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha02680.pow 1)))

@[irreducible]
def a02682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a01192 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02681 ^ 1)
theorem ha02682 : a02682.IsHomogeneous 418 := by
  unfold a02682
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha01192.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02681.pow 1)))

@[irreducible]
def a02683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02665 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02682 ^ 1)
theorem ha02683 : a02683.IsHomogeneous 672 := by
  unfold a02683
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02665.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02682.pow 1)))

@[irreducible]
def a02684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02667 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02683 ^ 1)
theorem ha02684 : a02684.IsHomogeneous 926 := by
  unfold a02684
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02667.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02683.pow 1)))

@[irreducible]
def a02685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a01194 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a02684 ^ 1)
theorem ha02685 : a02685.IsHomogeneous 1005 := by
  unfold a02685
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha01194.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha02684.pow 1)))

@[irreducible]
def a02686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02662 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a02685 ^ 1)
theorem ha02686 : a02686.IsHomogeneous 1084 := by
  unfold a02686
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02662.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha02685.pow 1)))

@[irreducible]
def a02687 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a02686 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02664 ^ 1)
theorem ha02687 : a02687.IsHomogeneous 1163 := by
  unfold a02687
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha02686.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02664.pow 1)))

@[irreducible]
def a02688 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02687 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a01196 ^ 1)
theorem ha02688 : a02688.IsHomogeneous 1271 := by
  unfold a02688
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02687.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha01196.pow 1)))

@[irreducible]
def a02689 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02688 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02661 ^ 1)
theorem ha02689 : a02689.IsHomogeneous 1361 := by
  unfold a02689
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02688.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02661.pow 1)))

@[irreducible]
def a02690 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a00836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01949 ^ 1)
theorem ha02690 : a02690.IsHomogeneous 755 := by
  unfold a02690
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00836.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a02691 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a02661 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02690 ^ 1)
theorem ha02691 : a02691.IsHomogeneous 1088 := by
  unfold a02691
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha02661.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02690.pow 1)))

@[irreducible]
def a02692 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a02689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02691 ^ 1)
theorem ha02692 : a02692.IsHomogeneous 1421 := by
  unfold a02692
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha02689.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02691.pow 1)))

@[irreducible]
def a02693 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a00850 ^ 1)
theorem ha02693 : a02693.IsHomogeneous 980 := by
  unfold a02693
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a02694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02687 ^ 1)
theorem ha02694 : a02694.IsHomogeneous 1247 := by
  unfold a02694
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha01196.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a02695 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a02694 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02693 ^ 1)
theorem ha02695 : a02695.IsHomogeneous 1313 := by
  unfold a02695
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02694.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02693.pow 1)))

@[irreducible]
def a02696 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a00850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01979 ^ 1)
theorem ha02696 : a02696.IsHomogeneous 683 := by
  unfold a02696
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00850.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a02697 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a02693 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02696 ^ 1)
theorem ha02697 : a02697.IsHomogeneous 1016 := by
  unfold a02697
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha02693.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02696.pow 1)))

@[irreducible]
def a02698 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a02695 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02697 ^ 1)
theorem ha02698 : a02698.IsHomogeneous 1349 := by
  unfold a02698
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha02695.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02697.pow 1)))

@[irreducible]
def a02699 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01290 ^ 1)
theorem ha02699 : a02699.IsHomogeneous 1096 := by
  unfold a02699
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a02700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a00804 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a01886 ^ 1)
theorem ha02700 : a02700.IsHomogeneous 1369 := by
  unfold a02700
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha00804.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a02701 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a02700 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02699 ^ 1)
theorem ha02701 : a02701.IsHomogeneous 1429 := by
  unfold a02701
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha02700.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02699.pow 1)))

@[irreducible]
def a02702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01288 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00491 ^ 1 * a00834 ^ 1)
theorem ha02702 : a02702.IsHomogeneous 361 := by
  unfold a02702
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01288.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00491.pow 1)).mul (ha00834.pow 1)))

@[irreducible]
def a02703 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00491 ^ 1 * a00834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00151 ^ 1 * a01946 ^ 1)
theorem ha02703 : a02703.IsHomogeneous 361 := by
  unfold a02703
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00491.pow 1)).mul (ha00834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a02704 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a02703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02702 ^ 1)
theorem ha02704 : a02704.IsHomogeneous 361 := by
  unfold a02704
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha02703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02702.pow 1)))

@[irreducible]
def a02705 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00303 ^ 1 * a01207 ^ 1)
theorem ha02705 : a02705.IsHomogeneous 132 := by
  unfold a02705
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00823.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00303.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a02706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha02706 : a02706.IsHomogeneous 12 := by
  unfold a02706
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a02707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02706 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00518 ^ 1)
theorem ha02707 : a02707.IsHomogeneous 12 := by
  unfold a02707
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00518.pow 1)))

@[irreducible]
def a02708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00864 ^ 1)
theorem ha02708 : a02708.IsHomogeneous 18 := by
  unfold a02708
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a02709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02708 ^ 1)
theorem ha02709 : a02709.IsHomogeneous 18 := by
  unfold a02709
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02706.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02708.pow 1)))

@[irreducible]
def a02710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02707 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02709 ^ 1)
theorem ha02710 : a02710.IsHomogeneous 18 := by
  unfold a02710
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02707.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02709.pow 1)))

@[irreducible]
def a02711 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00303 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02710 ^ 1)
theorem ha02711 : a02711.IsHomogeneous 126 := by
  unfold a02711
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00303.pow 1)).mul (ha01207.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a02712 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a02705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02711 ^ 1)
theorem ha02712 : a02712.IsHomogeneous 132 := by
  unfold a02712
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha02705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02711.pow 1)))

@[irreducible]
def a02713 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00455 ^ 1 * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a01923 ^ 1)
theorem ha02713 : a02713.IsHomogeneous 132 := by
  unfold a02713
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00455.pow 1)).mul (ha00823.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a02714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02705 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a02713 ^ 1)
theorem ha02714 : a02714.IsHomogeneous 132 := by
  unfold a02714
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02705.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha02713.pow 1)))

@[irreducible]
def a02715 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a02714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02712 ^ 1)
theorem ha02715 : a02715.IsHomogeneous 132 := by
  unfold a02715
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha02714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02712.pow 1)))

@[irreducible]
def a02716 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00298 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00480 ^ 1 * a00809 ^ 1)
theorem ha02716 : a02716.IsHomogeneous 175 := by
  unfold a02716
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00298.pow 1)).mul (ha01264.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00480.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a02717 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00148 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a00809 ^ 1)
theorem ha02717 : a02717.IsHomogeneous 166 := by
  unfold a02717
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a02718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02717 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02716 ^ 1)
theorem ha02718 : a02718.IsHomogeneous 175 := by
  unfold a02718
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02717.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02716.pow 1)))

@[irreducible]
def a02719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a00829 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a01223 ^ 1)
theorem ha02719 : a02719.IsHomogeneous 135 := by
  unfold a02719
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha00829.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01223.pow 1)))

@[irreducible]
def a02720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha02720 : a02720.IsHomogeneous 24 := by
  unfold a02720
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a02721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01213 ^ 1)
theorem ha02721 : a02721.IsHomogeneous 45 := by
  unfold a02721
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01213.pow 1)))

@[irreducible]
def a02722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02720 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02721 ^ 1)
theorem ha02722 : a02722.IsHomogeneous 48 := by
  unfold a02722
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02720.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02721.pow 1)))

@[irreducible]
def a02723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00865 ^ 1)
theorem ha02723 : a02723.IsHomogeneous 45 := by
  unfold a02723
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a02724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02723 ^ 1)
theorem ha02724 : a02724.IsHomogeneous 45 := by
  unfold a02724
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02723.pow 1)))

@[irreducible]
def a02725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01213 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02724 ^ 1)
theorem ha02725 : a02725.IsHomogeneous 51 := by
  unfold a02725
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01213.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02724.pow 1)))

@[irreducible]
def a02726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02725 ^ 1)
theorem ha02726 : a02726.IsHomogeneous 51 := by
  unfold a02726
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02725.pow 1)))

@[irreducible]
def a02727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02722 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a02726 ^ 1)
theorem ha02727 : a02727.IsHomogeneous 51 := by
  unfold a02727
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02722.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha02726.pow 1)))

@[irreducible]
def a02728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00133 ^ 1)
theorem ha02728 : a02728.IsHomogeneous 36 := by
  unfold a02728
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a02729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00129 ^ 1)
theorem ha02729 : a02729.IsHomogeneous 33 := by
  unfold a02729
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00133 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1)
theorem ha02730 : a02730.IsHomogeneous 30 := by
  unfold a02730
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02729 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a02728 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a02730 ^ 1)
theorem ha02731 : a02731.IsHomogeneous 36 := by
  unfold a02731
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha02728.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha02730.pow 1)))

@[irreducible]
def a02732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00317 ^ 1)
theorem ha02732 : a02732.IsHomogeneous 33 := by
  unfold a02732
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a02733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00042 ^ 1)
theorem ha02733 : a02733.IsHomogeneous 36 := by
  unfold a02733
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a02734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02733 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a02728 ^ 1)
theorem ha02734 : a02734.IsHomogeneous 36 := by
  unfold a02734
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02733.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha02728.pow 1)))

@[irreducible]
def a02735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00317 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00317 ^ 1)
theorem ha02735 : a02735.IsHomogeneous 33 := by
  unfold a02735
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a02736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02729 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02735 ^ 1) + (C ((7 : ℂ) / (10 : ℂ)) * a02732 ^ 1)
theorem ha02736 : a02736.IsHomogeneous 33 := by
  unfold a02736
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02735.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (10 : ℂ))).mul (ha02732.pow 1)))

@[irreducible]
def a02737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02736 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02731 ^ 1) + (C ((7 : ℂ) / (10 : ℂ)) * a02734 ^ 1)
theorem ha02737 : a02737.IsHomogeneous 36 := by
  unfold a02737
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02736.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02731.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (10 : ℂ))).mul (ha02734.pow 1)))

@[irreducible]
def a02738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00649 ^ 1)
theorem ha02738 : a02738.IsHomogeneous 12 := by
  unfold a02738
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a02739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha02739 : a02739.IsHomogeneous 12 := by
  unfold a02739
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a02740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a02739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a02738 ^ 1)
theorem ha02740 : a02740.IsHomogeneous 18 := by
  unfold a02740
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha02739.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha02738.pow 1)))

@[irreducible]
def a02741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a01607 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00649 ^ 1)
theorem ha02741 : a02741.IsHomogeneous 18 := by
  unfold a02741
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha01607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00649.pow 1)))

@[irreducible]
def a02742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a02738 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02741 ^ 1)
theorem ha02742 : a02742.IsHomogeneous 18 := by
  unfold a02742
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha02738.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02741.pow 1)))

@[irreducible]
def a02743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02740 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02742 ^ 1)
theorem ha02743 : a02743.IsHomogeneous 18 := by
  unfold a02743
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02742.pow 1)))

@[irreducible]
def a02744 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a02737 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02727 ^ 1) + (C ((7 : ℂ) / (116640 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00003 ^ 3 * a00004 ^ 6 * a02743 ^ 1)
theorem ha02744 : a02744.IsHomogeneous 51 := by
  unfold a02744
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha02737.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02727.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (116640 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha02743.pow 1)))

@[irreducible]
def a02745 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01223 ^ 1)
theorem ha02745 : a02745.IsHomogeneous 93 := by
  unfold a02745
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02744.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01223.pow 1)))

@[irreducible]
def a02746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02719 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02745 ^ 1)
theorem ha02746 : a02746.IsHomogeneous 135 := by
  unfold a02746
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02719.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02745.pow 1)))

@[irreducible]
def a02747 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00459 ^ 1 * a00829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a01938 ^ 1)
theorem ha02747 : a02747.IsHomogeneous 141 := by
  unfold a02747
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha00829.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a02748 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02719 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02747 ^ 1)
theorem ha02748 : a02748.IsHomogeneous 141 := by
  unfold a02748
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02719.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02747.pow 1)))

@[irreducible]
def a02749 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02746 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02748 ^ 1)
theorem ha02749 : a02749.IsHomogeneous 141 := by
  unfold a02749
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02746.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02748.pow 1)))

@[irreducible]
def a02750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00478 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a01261 ^ 1)
theorem ha02750 : a02750.IsHomogeneous 133 := by
  unfold a02750
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha01261.pow 1)))

@[irreducible]
def a02751 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00147 ^ 1 * a01841 ^ 1)
theorem ha02751 : a02751.IsHomogeneous 133 := by
  unfold a02751
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00478.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00147.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a02752 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a02751 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02750 ^ 1)
theorem ha02752 : a02752.IsHomogeneous 133 := by
  unfold a02752
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha02751.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02750.pow 1)))

@[irreducible]
def a02753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a00819 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a01228 ^ 1)
theorem ha02753 : a02753.IsHomogeneous 117 := by
  unfold a02753
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha00819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a02754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a01847 ^ 1) + (C ((1 : ℂ) / (4320 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha02754 : a02754.IsHomogeneous 15 := by
  unfold a02754
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha01847.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4320 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a02755 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a01228 ^ 1)
theorem ha02755 : a02755.IsHomogeneous 111 := by
  unfold a02755
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a02756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02753 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a02755 ^ 1)
theorem ha02756 : a02756.IsHomogeneous 117 := by
  unfold a02756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02753.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha02755.pow 1)))

@[irreducible]
def a02757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00461 ^ 1 * a00819 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00138 ^ 1 * a01917 ^ 1)
theorem ha02757 : a02757.IsHomogeneous 123 := by
  unfold a02757
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha00819.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00138.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a02758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02753 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02757 ^ 1)
theorem ha02758 : a02758.IsHomogeneous 123 := by
  unfold a02758
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02757.pow 1)))

@[irreducible]
def a02759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02756 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02758 ^ 1)
theorem ha02759 : a02759.IsHomogeneous 123 := by
  unfold a02759
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02758.pow 1)))

@[irreducible]
def a02760 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00476 ^ 1 * a00812 ^ 1)
theorem ha02760 : a02760.IsHomogeneous 124 := by
  unfold a02760
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a02761 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a00812 ^ 1)
theorem ha02761 : a02761.IsHomogeneous 118 := by
  unfold a02761
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha01903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a02762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02761 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02760 ^ 1)
theorem ha02762 : a02762.IsHomogeneous 124 := by
  unfold a02762
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02761.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02760.pow 1)))

@[irreducible]
def a02763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a00712 ^ 1)
theorem ha02763 : a02763.IsHomogeneous 81 := by
  unfold a02763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02764 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00139 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00465 ^ 1 * a00712 ^ 1)
theorem ha02764 : a02764.IsHomogeneous 81 := by
  unfold a02764
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00139.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00465.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02763 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a02764 ^ 1)
theorem ha02765 : a02765.IsHomogeneous 81 := by
  unfold a02765
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02763.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha02764.pow 1)))

@[irreducible]
def a02766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1)
theorem ha02766 : a02766.IsHomogeneous 39 := by
  unfold a02766
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a02767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha02767 : a02767.IsHomogeneous 33 := by
  unfold a02767
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a02768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02766 ^ 1)
theorem ha02768 : a02768.IsHomogeneous 39 := by
  unfold a02768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02766.pow 1)))

@[irreducible]
def a02769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1)
theorem ha02769 : a02769.IsHomogeneous 42 := by
  unfold a02769
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a02770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02766 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a02769 ^ 1)
theorem ha02770 : a02770.IsHomogeneous 45 := by
  unfold a02770
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02766.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha02769.pow 1)))

@[irreducible]
def a02771 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02770 ^ 1)
theorem ha02771 : a02771.IsHomogeneous 45 := by
  unfold a02771
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02768.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02770.pow 1)))

@[irreducible]
def a02772 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha02772 : a02772.IsHomogeneous 36 := by
  unfold a02772
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a02773 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00126 ^ 1 * a00864 ^ 1)
theorem ha02773 : a02773.IsHomogeneous 42 := by
  unfold a02773
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a02774 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02772 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02773 ^ 1)
theorem ha02774 : a02774.IsHomogeneous 42 := by
  unfold a02774
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02772.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02773.pow 1)))

@[irreducible]
def a02775 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00809 ^ 1)
theorem ha02775 : a02775.IsHomogeneous 33 := by
  unfold a02775
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00809.pow 1)))

@[irreducible]
def a02776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02775 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a02772 ^ 1)
theorem ha02776 : a02776.IsHomogeneous 39 := by
  unfold a02776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha02772.pow 1)))

@[irreducible]
def a02777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02776 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a02774 ^ 1)
theorem ha02777 : a02777.IsHomogeneous 45 := by
  unfold a02777
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02776.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha02774.pow 1)))

@[irreducible]
def a02778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02771 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a02777 ^ 1)
theorem ha02778 : a02778.IsHomogeneous 45 := by
  unfold a02778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha02777.pow 1)))

@[irreducible]
def a02779 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02778 ^ 1)
theorem ha02779 : a02779.IsHomogeneous 81 := by
  unfold a02779
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a02780 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02779 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02763 ^ 1)
theorem ha02780 : a02780.IsHomogeneous 81 := by
  unfold a02780
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02779.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02763.pow 1)))

@[irreducible]
def a02781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02765 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02780 ^ 1)
theorem ha02781 : a02781.IsHomogeneous 81 := by
  unfold a02781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02765.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02780.pow 1)))

@[irreducible]
def a02782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00241 ^ 1 * a00817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a00691 ^ 1)
theorem ha02782 : a02782.IsHomogeneous 107 := by
  unfold a02782
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a00691 ^ 1)
theorem ha02783 : a02783.IsHomogeneous 107 := by
  unfold a02783
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02782 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02783 ^ 1)
theorem ha02784 : a02784.IsHomogeneous 107 := by
  unfold a02784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02782.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02783.pow 1)))

@[irreducible]
def a02785 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a01914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00817 ^ 1)
theorem ha02785 : a02785.IsHomogeneous 100 := by
  unfold a02785
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha01914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a02786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a02785 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02782 ^ 1)
theorem ha02786 : a02786.IsHomogeneous 107 := by
  unfold a02786
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha02785.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02782.pow 1)))

@[irreducible]
def a02787 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02784 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02786 ^ 1)
theorem ha02787 : a02787.IsHomogeneous 107 := by
  unfold a02787
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02784.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02786.pow 1)))

@[irreducible]
def a02788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02787 ^ 1) + (C ((81 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02781 ^ 1)
theorem ha02788 : a02788.IsHomogeneous 107 := by
  unfold a02788
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02787.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02781.pow 1)))

@[irreducible]
def a02789 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a00712 ^ 1)
theorem ha02789 : a02789.IsHomogeneous 81 := by
  unfold a02789
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02790 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00141 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00469 ^ 1 * a00712 ^ 1)
theorem ha02790 : a02790.IsHomogeneous 81 := by
  unfold a02790
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00141.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00469.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02791 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02789 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a02790 ^ 1)
theorem ha02791 : a02791.IsHomogeneous 81 := by
  unfold a02791
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha02790.pow 1)))

@[irreducible]
def a02792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02771 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a02777 ^ 1)
theorem ha02792 : a02792.IsHomogeneous 45 := by
  unfold a02792
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha02777.pow 1)))

@[irreducible]
def a02793 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02792 ^ 1)
theorem ha02793 : a02793.IsHomogeneous 81 := by
  unfold a02793
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a02794 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02789 ^ 1)
theorem ha02794 : a02794.IsHomogeneous 81 := by
  unfold a02794
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02789.pow 1)))

@[irreducible]
def a02795 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02791 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02794 ^ 1)
theorem ha02795 : a02795.IsHomogeneous 81 := by
  unfold a02795
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02791.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02794.pow 1)))

@[irreducible]
def a02796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02787 ^ 1) + (C ((54 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02795 ^ 1)
theorem ha02796 : a02796.IsHomogeneous 107 := by
  unfold a02796
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02787.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02795.pow 1)))

@[irreducible]
def a02797 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a02796 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02788 ^ 1)
theorem ha02797 : a02797.IsHomogeneous 107 := by
  unfold a02797
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha02796.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02788.pow 1)))

@[irreducible]
def a02798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a00712 ^ 1)
theorem ha02798 : a02798.IsHomogeneous 81 := by
  unfold a02798
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02771 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a02777 ^ 1)
theorem ha02799 : a02799.IsHomogeneous 45 := by
  unfold a02799
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02771.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha02777.pow 1)))

@[irreducible]
def a02800 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02799 ^ 1)
theorem ha02800 : a02800.IsHomogeneous 81 := by
  unfold a02800
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a02801 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02800 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02798 ^ 1)
theorem ha02801 : a02801.IsHomogeneous 81 := by
  unfold a02801
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02800.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02798.pow 1)))

@[irreducible]
def a02802 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00144 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00473 ^ 1 * a00712 ^ 1)
theorem ha02802 : a02802.IsHomogeneous 81 := by
  unfold a02802
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00144.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00473.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02803 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02798 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a02802 ^ 1)
theorem ha02803 : a02803.IsHomogeneous 81 := by
  unfold a02803
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02798.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha02802.pow 1)))

@[irreducible]
def a02804 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02803 ^ 1)
theorem ha02804 : a02804.IsHomogeneous 81 := by
  unfold a02804
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02801.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02803.pow 1)))

@[irreducible]
def a02805 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02787 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02804 ^ 1)
theorem ha02805 : a02805.IsHomogeneous 107 := by
  unfold a02805
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02787.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02804.pow 1)))

@[irreducible]
def a02806 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a02805 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02797 ^ 1)
theorem ha02806 : a02806.IsHomogeneous 107 := by
  unfold a02806
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha02805.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02797.pow 1)))

@[irreducible]
def a02807 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00299 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a02806 ^ 1)
theorem ha02807 : a02807.IsHomogeneous 125 := by
  unfold a02807
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00299.pow 1)).mul (ha01258.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha02806.pow 1)))

@[irreducible]
def a02808 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02807 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a02760 ^ 1)
theorem ha02808 : a02808.IsHomogeneous 125 := by
  unfold a02808
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02807.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha02760.pow 1)))

@[irreducible]
def a02809 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02808 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a02762 ^ 1)
theorem ha02809 : a02809.IsHomogeneous 125 := by
  unfold a02809
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02808.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha02762.pow 1)))

@[irreducible]
def a02810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02809 ^ 1) + (C ((72 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a02759 ^ 1)
theorem ha02810 : a02810.IsHomogeneous 131 := by
  unfold a02810
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02809.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02759.pow 1)))

@[irreducible]
def a02811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02810 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 4 * a01261 ^ 1)
theorem ha02811 : a02811.IsHomogeneous 137 := by
  unfold a02811
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02810.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 4)).mul (ha01261.pow 1)))

@[irreducible]
def a02812 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02811 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a02750 ^ 1)
theorem ha02812 : a02812.IsHomogeneous 137 := by
  unfold a02812
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha02750.pow 1)))

@[irreducible]
def a02813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02812 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a02752 ^ 1)
theorem ha02813 : a02813.IsHomogeneous 137 := by
  unfold a02813
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha02752.pow 1)))

@[irreducible]
def a02814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a02813 ^ 1) + (C ((243 : ℂ) / (625 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a02749 ^ 1)
theorem ha02814 : a02814.IsHomogeneous 149 := by
  unfold a02814
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha02813.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (625 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02749.pow 1)))

@[irreducible]
def a02815 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a02814 ^ 1)
theorem ha02815 : a02815.IsHomogeneous 181 := by
  unfold a02815
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha01264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a02816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02815 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02716 ^ 1)
theorem ha02816 : a02816.IsHomogeneous 181 := by
  unfold a02816
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02815.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02716.pow 1)))

@[irreducible]
def a02817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02816 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02718 ^ 1)
theorem ha02817 : a02817.IsHomogeneous 181 := by
  unfold a02817
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02816.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02718.pow 1)))

@[irreducible]
def a02818 : Poly := (C ((-2 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a02715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02817 ^ 1)
theorem ha02818 : a02818.IsHomogeneous 181 := by
  unfold a02818
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha02715.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02817.pow 1)))

@[irreducible]
def a02819 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a00836 ^ 1)
theorem ha02819 : a02819.IsHomogeneous 319 := by
  unfold a02819
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a02820 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1)
theorem ha02820 : a02820.IsHomogeneous 84 := by
  unfold a02820
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)))

@[irreducible]
def a02821 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00100 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00316 ^ 1)
theorem ha02821 : a02821.IsHomogeneous 48 := by
  unfold a02821
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00100.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a02822 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a02821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02820 ^ 1)
theorem ha02822 : a02822.IsHomogeneous 84 := by
  unfold a02822
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha02821.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02820.pow 1)))

@[irreducible]
def a02823 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a00831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01941 ^ 1)
theorem ha02823 : a02823.IsHomogeneous 126 := by
  unfold a02823
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha00831.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01941.pow 1)))

@[irreducible]
def a02824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a02820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02823 ^ 1)
theorem ha02824 : a02824.IsHomogeneous 126 := by
  unfold a02824
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha02820.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02823.pow 1)))

@[irreducible]
def a02825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a02822 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02824 ^ 1)
theorem ha02825 : a02825.IsHomogeneous 126 := by
  unfold a02825
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha02822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02824.pow 1)))

@[irreducible]
def a02826 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00317 ^ 1 * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01281 ^ 1)
theorem ha02826 : a02826.IsHomogeneous 148 := by
  unfold a02826
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00317.pow 1)).mul (ha00487.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a02827 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00487 ^ 1)
theorem ha02827 : a02827.IsHomogeneous 106 := by
  unfold a02827
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00487.pow 1)))

@[irreducible]
def a02828 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02826 ^ 1)
theorem ha02828 : a02828.IsHomogeneous 148 := by
  unfold a02828
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02827.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02826.pow 1)))

@[irreducible]
def a02829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00484 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00260 ^ 1 * a01275 ^ 1)
theorem ha02829 : a02829.IsHomogeneous 133 := by
  unfold a02829
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00484.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00260.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02830 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00484 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a01702 ^ 1)
theorem ha02830 : a02830.IsHomogeneous 130 := by
  unfold a02830
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00484.pow 1)).mul (ha00712.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a02831 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02830 ^ 1)
theorem ha02831 : a02831.IsHomogeneous 133 := by
  unfold a02831
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02829.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02830.pow 1)))

@[irreducible]
def a02832 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00241 ^ 1 * a00712 ^ 1)
theorem ha02832 : a02832.IsHomogeneous 95 := by
  unfold a02832
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00241.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02833 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00691 ^ 1)
theorem ha02833 : a02833.IsHomogeneous 95 := by
  unfold a02833
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02832 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02833 ^ 1)
theorem ha02834 : a02834.IsHomogeneous 95 := by
  unfold a02834
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02832.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02833.pow 1)))

@[irreducible]
def a02835 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01702 ^ 1)
theorem ha02835 : a02835.IsHomogeneous 94 := by
  unfold a02835
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a02836 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a02835 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02832 ^ 1)
theorem ha02836 : a02836.IsHomogeneous 95 := by
  unfold a02836
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha02835.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02832.pow 1)))

@[irreducible]
def a02837 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02836 ^ 1)
theorem ha02837 : a02837.IsHomogeneous 95 := by
  unfold a02837
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02834.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02836.pow 1)))

@[irreducible]
def a02838 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01275 ^ 1)
theorem ha02838 : a02838.IsHomogeneous 133 := by
  unfold a02838
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02829 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a02838 ^ 1)
theorem ha02839 : a02839.IsHomogeneous 133 := by
  unfold a02839
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha02838.pow 1)))

@[irreducible]
def a02840 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02831 ^ 1)
theorem ha02840 : a02840.IsHomogeneous 133 := by
  unfold a02840
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02831.pow 1)))

@[irreducible]
def a02841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00260 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00829 ^ 1)
theorem ha02841 : a02841.IsHomogeneous 133 := by
  unfold a02841
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a02842 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00691 ^ 1)
theorem ha02842 : a02842.IsHomogeneous 95 := by
  unfold a02842
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02842 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02841 ^ 1)
theorem ha02843 : a02843.IsHomogeneous 133 := by
  unfold a02843
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02842.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02841.pow 1)))

@[irreducible]
def a02844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00241 ^ 1 * a00829 ^ 1)
theorem ha02844 : a02844.IsHomogeneous 133 := by
  unfold a02844
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00241.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a02845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02841 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a02844 ^ 1)
theorem ha02845 : a02845.IsHomogeneous 133 := by
  unfold a02845
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha02844.pow 1)))

@[irreducible]
def a02846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02843 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02845 ^ 1)
theorem ha02846 : a02846.IsHomogeneous 133 := by
  unfold a02846
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02843.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02845.pow 1)))

@[irreducible]
def a02847 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02846 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02840 ^ 1)
theorem ha02847 : a02847.IsHomogeneous 133 := by
  unfold a02847
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02840.pow 1)))

@[irreducible]
def a02848 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01281 ^ 1)
theorem ha02848 : a02848.IsHomogeneous 157 := by
  unfold a02848
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha02847.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a02849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02826 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02848 ^ 1)
theorem ha02849 : a02849.IsHomogeneous 157 := by
  unfold a02849
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02826.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02848.pow 1)))

@[irreducible]
def a02850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02828 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02849 ^ 1)
theorem ha02850 : a02850.IsHomogeneous 157 := by
  unfold a02850
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02828.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02849.pow 1)))

@[irreducible]
def a02851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02850 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02825 ^ 1)
theorem ha02851 : a02851.IsHomogeneous 157 := by
  unfold a02851
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02850.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02825.pow 1)))

@[irreducible]
def a02852 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02851 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a01284 ^ 1)
theorem ha02852 : a02852.IsHomogeneous 265 := by
  unfold a02852
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02851.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha01284.pow 1)))

@[irreducible]
def a02853 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a02852 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02819 ^ 1)
theorem ha02853 : a02853.IsHomogeneous 319 := by
  unfold a02853
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha02852.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02819.pow 1)))

@[irreducible]
def a02854 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a00836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a01949 ^ 1)
theorem ha02854 : a02854.IsHomogeneous 343 := by
  unfold a02854
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha00836.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a02855 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a02819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02854 ^ 1)
theorem ha02855 : a02855.IsHomogeneous 343 := by
  unfold a02855
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha02819.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02854.pow 1)))

@[irreducible]
def a02856 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a02853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02855 ^ 1)
theorem ha02856 : a02856.IsHomogeneous 343 := by
  unfold a02856
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha02853.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02855.pow 1)))

@[irreducible]
def a02857 : Poly := (C ((-25 : ℂ) / (972 : ℂ)) * a00042 ^ 3 * a00100 ^ 3 * a02818 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a02856 ^ 1)
theorem ha02857 : a02857.IsHomogeneous 361 := by
  unfold a02857
  exact (((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (972 : ℂ))).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha02818.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha02856.pow 1)))

@[irreducible]
def a02858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01288 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02857 ^ 1)
theorem ha02858 : a02858.IsHomogeneous 361 := by
  unfold a02858
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02857.pow 1)))

@[irreducible]
def a02859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02858 ^ 1)
theorem ha02859 : a02859.IsHomogeneous 361 := by
  unfold a02859
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02858.pow 1)))

@[irreducible]
def a02860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02704 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02859 ^ 1)
theorem ha02860 : a02860.IsHomogeneous 361 := by
  unfold a02860
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02704.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02859.pow 1)))

@[irreducible]
def a02861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02860 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a01290 ^ 1)
theorem ha02861 : a02861.IsHomogeneous 787 := by
  unfold a02861
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02860.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a02862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02861 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a02699 ^ 1)
theorem ha02862 : a02862.IsHomogeneous 1120 := by
  unfold a02862
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha02699.pow 1)))

@[irreducible]
def a02863 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02862 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a02701 ^ 1)
theorem ha02863 : a02863.IsHomogeneous 1453 := by
  unfold a02863
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02862.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha02701.pow 1)))

@[irreducible]
def a02864 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01313 ^ 1)
theorem ha02864 : a02864.IsHomogeneous 1012 := by
  unfold a02864
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a02865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a00804 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a01886 ^ 1)
theorem ha02865 : a02865.IsHomogeneous 1309 := by
  unfold a02865
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha00804.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a02866 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a02865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02864 ^ 1)
theorem ha02866 : a02866.IsHomogeneous 1345 := by
  unfold a02866
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha02865.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02864.pow 1)))

@[irreducible]
def a02867 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00500 ^ 1 * a00848 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01311 ^ 1)
theorem ha02867 : a02867.IsHomogeneous 253 := by
  unfold a02867
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)).mul (ha00848.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01311.pow 1)))

@[irreducible]
def a02868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a01976 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00500 ^ 1 * a00848 ^ 1)
theorem ha02868 : a02868.IsHomogeneous 253 := by
  unfold a02868
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01976.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)).mul (ha00848.pow 1)))

@[irreducible]
def a02869 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a02868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02867 ^ 1)
theorem ha02869 : a02869.IsHomogeneous 253 := by
  unfold a02869
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha02868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02867.pow 1)))

@[irreducible]
def a02870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00497 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01304 ^ 1)
theorem ha02870 : a02870.IsHomogeneous 84 := by
  unfold a02870
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00497.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01304.pow 1)))

@[irreducible]
def a02871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00494 ^ 1 * a00812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a01298 ^ 1)
theorem ha02871 : a02871.IsHomogeneous 63 := by
  unfold a02871
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a02872 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a00812 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a01903 ^ 1)
theorem ha02872 : a02872.IsHomogeneous 57 := by
  unfold a02872
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha00812.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a02873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02872 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02871 ^ 1)
theorem ha02873 : a02873.IsHomogeneous 63 := by
  unfold a02873
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02872.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02871.pow 1)))

@[irreducible]
def a02874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00298 ^ 1 * a01207 ^ 1)
theorem ha02874 : a02874.IsHomogeneous 45 := by
  unfold a02874
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha00809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00298.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a02875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a01207 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00126 ^ 1 * a02710 ^ 1)
theorem ha02875 : a02875.IsHomogeneous 48 := by
  unfold a02875
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a02876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02874 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a02875 ^ 1)
theorem ha02876 : a02876.IsHomogeneous 51 := by
  unfold a02876
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02874.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha02875.pow 1)))

@[irreducible]
def a02877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a01896 ^ 1)
theorem ha02877 : a02877.IsHomogeneous 39 := by
  unfold a02877
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a02878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02874 ^ 1)
theorem ha02878 : a02878.IsHomogeneous 45 := by
  unfold a02878
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02877.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02874.pow 1)))

@[irreducible]
def a02879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02878 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02876 ^ 1)
theorem ha02879 : a02879.IsHomogeneous 51 := by
  unfold a02879
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02876.pow 1)))

@[irreducible]
def a02880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00299 ^ 1 * a01298 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00127 ^ 1 * a02879 ^ 1)
theorem ha02880 : a02880.IsHomogeneous 69 := by
  unfold a02880
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha01298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00127.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a02881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02880 ^ 1)
theorem ha02881 : a02881.IsHomogeneous 69 := by
  unfold a02881
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02871.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02880.pow 1)))

@[irreducible]
def a02882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02881 ^ 1)
theorem ha02882 : a02882.IsHomogeneous 69 := by
  unfold a02882
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02873.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02881.pow 1)))

@[irreducible]
def a02883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a01228 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00461 ^ 1 * a00841 ^ 1)
theorem ha02883 : a02883.IsHomogeneous 75 := by
  unfold a02883
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00461.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a02884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00126 ^ 1 * a02754 ^ 1)
theorem ha02884 : a02884.IsHomogeneous 45 := by
  unfold a02884
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00126.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a02885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02883 ^ 1)
theorem ha02885 : a02885.IsHomogeneous 75 := by
  unfold a02885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02883.pow 1)))

@[irreducible]
def a02886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a01962 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00461 ^ 1 * a00841 ^ 1)
theorem ha02886 : a02886.IsHomogeneous 75 := by
  unfold a02886
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha01962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00461.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a02887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02883 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a02886 ^ 1)
theorem ha02887 : a02887.IsHomogeneous 75 := by
  unfold a02887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha02886.pow 1)))

@[irreducible]
def a02888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02887 ^ 1)
theorem ha02888 : a02888.IsHomogeneous 75 := by
  unfold a02888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02887.pow 1)))

@[irreducible]
def a02889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02882 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02888 ^ 1)
theorem ha02889 : a02889.IsHomogeneous 75 := by
  unfold a02889
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02882.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02888.pow 1)))

@[irreducible]
def a02890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02889 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01304 ^ 1)
theorem ha02890 : a02890.IsHomogeneous 81 := by
  unfold a02890
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01304.pow 1)))

@[irreducible]
def a02891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02890 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02870 ^ 1)
theorem ha02891 : a02891.IsHomogeneous 87 := by
  unfold a02891
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02870.pow 1)))

@[irreducible]
def a02892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00152 ^ 1 * a01841 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00497 ^ 1)
theorem ha02892 : a02892.IsHomogeneous 90 := by
  unfold a02892
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00152.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00497.pow 1)))

@[irreducible]
def a02893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02892 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a02870 ^ 1)
theorem ha02893 : a02893.IsHomogeneous 90 := by
  unfold a02893
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02892.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha02870.pow 1)))

@[irreducible]
def a02894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02891 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a02893 ^ 1)
theorem ha02894 : a02894.IsHomogeneous 93 := by
  unfold a02894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02891.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha02893.pow 1)))

@[irreducible]
def a02895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a00850 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a01275 ^ 1)
theorem ha02895 : a02895.IsHomogeneous 247 := by
  unfold a02895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha00850.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02896 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a01275 ^ 1)
theorem ha02896 : a02896.IsHomogeneous 181 := by
  unfold a02896
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02895 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a02896 ^ 1)
theorem ha02897 : a02897.IsHomogeneous 247 := by
  unfold a02897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02895.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02896.pow 1)))

@[irreducible]
def a02898 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a00850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01979 ^ 1)
theorem ha02898 : a02898.IsHomogeneous 247 := by
  unfold a02898
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha00850.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a02899 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02898 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02895 ^ 1)
theorem ha02899 : a02899.IsHomogeneous 247 := by
  unfold a02899
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02895.pow 1)))

@[irreducible]
def a02900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02897 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02899 ^ 1)
theorem ha02900 : a02900.IsHomogeneous 247 := by
  unfold a02900
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02897.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02899.pow 1)))

@[irreducible]
def a02901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02900 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 4 * a02894 ^ 1)
theorem ha02901 : a02901.IsHomogeneous 253 := by
  unfold a02901
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02900.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 4)).mul (ha02894.pow 1)))

@[irreducible]
def a02902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01311 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02901 ^ 1)
theorem ha02902 : a02902.IsHomogeneous 253 := by
  unfold a02902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01311.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02901.pow 1)))

@[irreducible]
def a02903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02902 ^ 1)
theorem ha02903 : a02903.IsHomogeneous 253 := by
  unfold a02903
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02867.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02902.pow 1)))

@[irreducible]
def a02904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02869 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02903 ^ 1)
theorem ha02904 : a02904.IsHomogeneous 253 := by
  unfold a02904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02869.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02903.pow 1)))

@[irreducible]
def a02905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a01313 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02904 ^ 1)
theorem ha02905 : a02905.IsHomogeneous 679 := by
  unfold a02905
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha01313.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a02906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02864 ^ 1)
theorem ha02906 : a02906.IsHomogeneous 1012 := by
  unfold a02906
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02864.pow 1)))

@[irreducible]
def a02907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02906 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02866 ^ 1)
theorem ha02907 : a02907.IsHomogeneous 1345 := by
  unfold a02907
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02866.pow 1)))

@[irreducible]
def a02908 : Poly := (C ((-128 : ℂ) / (27 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 4 * a02907 ^ 1) + (C ((-3 : ℂ) / (2 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a02863 ^ 1) + (C ((-2 : ℂ) / (3 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 4 * a02698 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a02692 ^ 1)
theorem ha02908 : a02908.IsHomogeneous 1463 := by
  unfold a02908
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-128 : ℂ) / (27 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02907.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha02863.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02698.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha02692.pow 1)))

@[irreducible]
def a02909 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00853 ^ 1 * a00881 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a01983 ^ 1)
theorem ha02909 : a02909.IsHomogeneous 1530 := by
  unfold a02909
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00853.pow 1)).mul (ha00881.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha01983.pow 1)))

@[irreducible]
def a02910 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00312 ^ 1 * a02043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00853 ^ 1 * a00881 ^ 1)
theorem ha02910 : a02910.IsHomogeneous 1233 := by
  unfold a02910
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00312.pow 1)).mul (ha02043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00853.pow 1)).mul (ha00881.pow 1)))

@[irreducible]
def a02911 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02910 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a02909 ^ 1)
theorem ha02911 : a02911.IsHomogeneous 1590 := by
  unfold a02911
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02910.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha02909.pow 1)))

@[irreducible]
def a02912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a00836 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a01886 ^ 1)
theorem ha02912 : a02912.IsHomogeneous 1350 := by
  unfold a02912
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha00836.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a02913 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a00836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01949 ^ 1)
theorem ha02913 : a02913.IsHomogeneous 1077 := by
  unfold a02913
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha00836.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a02914 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a02912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02913 ^ 1)
theorem ha02914 : a02914.IsHomogeneous 1410 := by
  unfold a02914
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha02912.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02913.pow 1)))

@[irreducible]
def a02915 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a00802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00295 ^ 1 * a01707 ^ 1)
theorem ha02915 : a02915.IsHomogeneous 898 := by
  unfold a02915
  exact (((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha00802.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00295.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a02916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a00802 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a01883 ^ 1)
theorem ha02916 : a02916.IsHomogeneous 1073 := by
  unfold a02916
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha00802.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01883.pow 1)))

@[irreducible]
def a02917 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a02916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02915 ^ 1)
theorem ha02917 : a02917.IsHomogeneous 1152 := by
  unfold a02917
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha02916.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02915.pow 1)))

@[irreducible]
def a02918 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a00261 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a01320 ^ 1)
theorem ha02918 : a02918.IsHomogeneous 340 := by
  unfold a02918
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha01320.pow 1)))

@[irreducible]
def a02919 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a01705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00714 ^ 1)
theorem ha02919 : a02919.IsHomogeneous 255 := by
  unfold a02919
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha01705.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00714.pow 1)))

@[irreducible]
def a02920 : Poly := (C ((-5 : ℂ) / (256 : ℂ)) * a00714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 2)
theorem ha02920 : a02920.IsHomogeneous 170 := by
  unfold a02920
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (256 : ℂ))).mul (ha00714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a02921 : Poly := (C ((-256 : ℂ) / (5 : ℂ)) * a02920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1)
theorem ha02921 : a02921.IsHomogeneous 170 := by
  unfold a02921
  exact (((isHomogeneous_C (σ := Fin 6) ((-256 : ℂ) / (5 : ℂ))).mul (ha02920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)))

@[irreducible]
def a02922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a02921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02919 ^ 1)
theorem ha02922 : a02922.IsHomogeneous 255 := by
  unfold a02922
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha02921.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02919.pow 1)))

@[irreducible]
def a02923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a02922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1 * a01320 ^ 1)
theorem ha02923 : a02923.IsHomogeneous 340 := by
  unfold a02923
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha02922.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)).mul (ha01320.pow 1)))

@[irreducible]
def a02924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02918 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02923 ^ 1)
theorem ha02924 : a02924.IsHomogeneous 340 := by
  unfold a02924
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02918.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02923.pow 1)))

@[irreducible]
def a02925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00261 ^ 1 * a01703 ^ 1) + (C ((5 : ℂ) / (32 : ℂ)) * a00713 ^ 2)
theorem ha02925 : a02925.IsHomogeneous 180 := by
  unfold a02925
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00261.pow 1)).mul (ha01703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (32 : ℂ))).mul (ha00713.pow 2)))

@[irreducible]
def a02926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00157 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00513 ^ 1)
theorem ha02926 : a02926.IsHomogeneous 30 := by
  unfold a02926
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00513.pow 1)))

@[irreducible]
def a02927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a01340 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00513 ^ 1)
theorem ha02927 : a02927.IsHomogeneous 30 := by
  unfold a02927
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha01340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00513.pow 1)))

@[irreducible]
def a02928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02926 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02927 ^ 1)
theorem ha02928 : a02928.IsHomogeneous 30 := by
  unfold a02928
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02926.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02927.pow 1)))

@[irreducible]
def a02929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha02929 : a02929.IsHomogeneous 6 := by
  unfold a02929
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a02930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02929 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha02930 : a02930.IsHomogeneous 6 := by
  unfold a02930
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02929.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a02931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02930 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha02931 : a02931.IsHomogeneous 6 := by
  unfold a02931
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a02932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a02931 ^ 1)
theorem ha02932 : a02932.IsHomogeneous 6 := by
  unfold a02932
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha02931.pow 1)))

@[irreducible]
def a02933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01333 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a02932 ^ 1)
theorem ha02933 : a02933.IsHomogeneous 6 := by
  unfold a02933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha02932.pow 1)))

@[irreducible]
def a02934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02933 ^ 1)
theorem ha02934 : a02934.IsHomogeneous 6 := by
  unfold a02934
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02933.pow 1)))

@[irreducible]
def a02935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02934 ^ 1)
theorem ha02935 : a02935.IsHomogeneous 6 := by
  unfold a02935
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02934.pow 1)))

@[irreducible]
def a02936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a02935 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00157 ^ 1 * a01327 ^ 1)
theorem ha02936 : a02936.IsHomogeneous 18 := by
  unfold a02936
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00157.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a02937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02936 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a02926 ^ 1)
theorem ha02937 : a02937.IsHomogeneous 30 := by
  unfold a02937
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha02926.pow 1)))

@[irreducible]
def a02938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02928 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a02937 ^ 1)
theorem ha02938 : a02938.IsHomogeneous 30 := by
  unfold a02938
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha02937.pow 1)))

@[irreducible]
def a02939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00511 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha02939 : a02939.IsHomogeneous 12 := by
  unfold a02939
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a02940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00014 ^ 1)
theorem ha02940 : a02940.IsHomogeneous 6 := by
  unfold a02940
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a02941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02939 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02940 ^ 1)
theorem ha02941 : a02941.IsHomogeneous 12 := by
  unfold a02941
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02939.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02940.pow 1)))

@[irreducible]
def a02942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00511 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01337 ^ 1)
theorem ha02942 : a02942.IsHomogeneous 18 := by
  unfold a02942
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01337.pow 1)))

@[irreducible]
def a02943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02942 ^ 1)
theorem ha02943 : a02943.IsHomogeneous 18 := by
  unfold a02943
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02939.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02942.pow 1)))

@[irreducible]
def a02944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02943 ^ 1)
theorem ha02944 : a02944.IsHomogeneous 18 := by
  unfold a02944
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02943.pow 1)))

@[irreducible]
def a02945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 2)
theorem ha02945 : a02945.IsHomogeneous 18 := by
  unfold a02945
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 2)))

@[irreducible]
def a02946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02931 ^ 1)
theorem ha02946 : a02946.IsHomogeneous 6 := by
  unfold a02946
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)))

@[irreducible]
def a02947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02946 ^ 1)
theorem ha02947 : a02947.IsHomogeneous 6 := by
  unfold a02947
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02946.pow 1)))

@[irreducible]
def a02948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02947 ^ 1)
theorem ha02948 : a02948.IsHomogeneous 6 := by
  unfold a02948
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02947.pow 1)))

@[irreducible]
def a02949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02948 ^ 1)
theorem ha02949 : a02949.IsHomogeneous 6 := by
  unfold a02949
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02948.pow 1)))

@[irreducible]
def a02950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a02949 ^ 1)
theorem ha02950 : a02950.IsHomogeneous 12 := by
  unfold a02950
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a02951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02945 ^ 1)
theorem ha02951 : a02951.IsHomogeneous 18 := by
  unfold a02951
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02945.pow 1)))

@[irreducible]
def a02952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02945 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02951 ^ 1)
theorem ha02952 : a02952.IsHomogeneous 18 := by
  unfold a02952
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02945.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02951.pow 1)))

@[irreducible]
def a02953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02952 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01337 ^ 1)
theorem ha02953 : a02953.IsHomogeneous 24 := by
  unfold a02953
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02952.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01337.pow 1)))

@[irreducible]
def a02954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02942 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a02953 ^ 1)
theorem ha02954 : a02954.IsHomogeneous 24 := by
  unfold a02954
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02942.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha02953.pow 1)))

@[irreducible]
def a02955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02954 ^ 1)
theorem ha02955 : a02955.IsHomogeneous 24 := by
  unfold a02955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02954.pow 1)))

@[irreducible]
def a02956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02944 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02955 ^ 1)
theorem ha02956 : a02956.IsHomogeneous 24 := by
  unfold a02956
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02944.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02955.pow 1)))

@[irreducible]
def a02957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01340 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a02956 ^ 1)
theorem ha02957 : a02957.IsHomogeneous 24 := by
  unfold a02957
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha02956.pow 1)))

@[irreducible]
def a02958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02927 ^ 1)
theorem ha02958 : a02958.IsHomogeneous 30 := by
  unfold a02958
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02927.pow 1)))

@[irreducible]
def a02959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02928 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02958 ^ 1)
theorem ha02959 : a02959.IsHomogeneous 30 := by
  unfold a02959
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02928.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02958.pow 1)))

@[irreducible]
def a02960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02959 ^ 1)
theorem ha02960 : a02960.IsHomogeneous 30 := by
  unfold a02960
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02959.pow 1)))

@[irreducible]
def a02961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1)
theorem ha02961 : a02961.IsHomogeneous 18 := by
  unfold a02961
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)))

@[irreducible]
def a02962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a00316 ^ 1)
theorem ha02962 : a02962.IsHomogeneous 24 := by
  unfold a02962
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a02963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha02963 : a02963.IsHomogeneous 12 := by
  unfold a02963
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a02964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02962 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02963 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02961 ^ 1)
theorem ha02964 : a02964.IsHomogeneous 24 := by
  unfold a02964
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02962.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02963.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02961.pow 1)))

@[irreducible]
def a02965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00520 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha02965 : a02965.IsHomogeneous 12 := by
  unfold a02965
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00520.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a02966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01356 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00520 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00520 ^ 1)
theorem ha02966 : a02966.IsHomogeneous 24 := by
  unfold a02966
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a02967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02966 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02965 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02961 ^ 1)
theorem ha02967 : a02967.IsHomogeneous 24 := by
  unfold a02967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02966.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02965.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02961.pow 1)))

@[irreducible]
def a02968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha02968 : a02968.IsHomogeneous 12 := by
  unfold a02968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a02969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02968 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02963 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02965 ^ 1)
theorem ha02969 : a02969.IsHomogeneous 18 := by
  unfold a02969
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02968.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02963.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02965.pow 1)))

@[irreducible]
def a02970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02964 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02967 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a02969 ^ 1)
theorem ha02970 : a02970.IsHomogeneous 24 := by
  unfold a02970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02964.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02967.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha02969.pow 1)))

@[irreducible]
def a02971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00025 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00520 ^ 1)
theorem ha02971 : a02971.IsHomogeneous 24 := by
  unfold a02971
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a02972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00025 ^ 1 * a01356 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1)
theorem ha02972 : a02972.IsHomogeneous 24 := by
  unfold a02972
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00025.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a02973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02971 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02961 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a02972 ^ 1)
theorem ha02973 : a02973.IsHomogeneous 24 := by
  unfold a02973
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02971.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02961.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha02972.pow 1)))

@[irreducible]
def a02974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00864 ^ 1)
theorem ha02974 : a02974.IsHomogeneous 30 := by
  unfold a02974
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a02975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02974 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02962 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02971 ^ 1)
theorem ha02975 : a02975.IsHomogeneous 30 := by
  unfold a02975
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02974.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02962.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02971.pow 1)))

@[irreducible]
def a02976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02975 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02964 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02973 ^ 1)
theorem ha02976 : a02976.IsHomogeneous 30 := by
  unfold a02976
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02975.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02964.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02973.pow 1)))

@[irreducible]
def a02977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha02977 : a02977.IsHomogeneous 6 := by
  unfold a02977
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a02978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02977 ^ 1)
theorem ha02978 : a02978.IsHomogeneous 12 := by
  unfold a02978
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02977.pow 1)))

@[irreducible]
def a02979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00864 ^ 1)
theorem ha02979 : a02979.IsHomogeneous 12 := by
  unfold a02979
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00864.pow 1)))

@[irreducible]
def a02980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02977 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02979 ^ 1)
theorem ha02980 : a02980.IsHomogeneous 12 := by
  unfold a02980
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02977.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02979.pow 1)))

@[irreducible]
def a02981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02978 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02980 ^ 1)
theorem ha02981 : a02981.IsHomogeneous 18 := by
  unfold a02981
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02980.pow 1)))

@[irreducible]
def a02982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00864 ^ 1)
theorem ha02982 : a02982.IsHomogeneous 18 := by
  unfold a02982
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00864.pow 1)))

@[irreducible]
def a02983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02982 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02979 ^ 1)
theorem ha02983 : a02983.IsHomogeneous 18 := by
  unfold a02983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02979.pow 1)))

@[irreducible]
def a02984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02983 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02980 ^ 1)
theorem ha02984 : a02984.IsHomogeneous 18 := by
  unfold a02984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02983.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02980.pow 1)))

@[irreducible]
def a02985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02981 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02984 ^ 1)
theorem ha02985 : a02985.IsHomogeneous 18 := by
  unfold a02985
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02984.pow 1)))

@[irreducible]
def a02986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01356 ^ 1)
theorem ha02986 : a02986.IsHomogeneous 30 := by
  unfold a02986
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a02987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02986 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02966 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02972 ^ 1)
theorem ha02987 : a02987.IsHomogeneous 30 := by
  unfold a02987
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02986.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02966.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02972.pow 1)))

@[irreducible]
def a02988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02987 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02967 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02973 ^ 1)
theorem ha02988 : a02988.IsHomogeneous 30 := by
  unfold a02988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02987.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02967.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02973.pow 1)))

@[irreducible]
def a02989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02976 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02988 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02970 ^ 1)
theorem ha02989 : a02989.IsHomogeneous 30 := by
  unfold a02989
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02988.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02970.pow 1)))

@[irreducible]
def a02990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00007 ^ 2 * a02989 ^ 1) + (C ((4 : ℂ) / (405 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00005 ^ 3 * a02960 ^ 1)
theorem ha02990 : a02990.IsHomogeneous 45 := by
  unfold a02990
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00007.pow 2)).mul (ha02989.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (405 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00005.pow 3)).mul (ha02960.pow 1)))

@[irreducible]
def a02991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00528 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a01327 ^ 1)
theorem ha02991 : a02991.IsHomogeneous 30 := by
  unfold a02991
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00528.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a02992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01373 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00528 ^ 1)
theorem ha02992 : a02992.IsHomogeneous 30 := by
  unfold a02992
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00528.pow 1)))

@[irreducible]
def a02993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02991 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02992 ^ 1)
theorem ha02993 : a02993.IsHomogeneous 30 := by
  unfold a02993
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02992.pow 1)))

@[irreducible]
def a02994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00161 ^ 1 * a01327 ^ 1)
theorem ha02994 : a02994.IsHomogeneous 24 := by
  unfold a02994
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00161.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a02995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02991 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a02994 ^ 1)
theorem ha02995 : a02995.IsHomogeneous 30 := by
  unfold a02995
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02991.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha02994.pow 1)))

@[irreducible]
def a02996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02993 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02995 ^ 1)
theorem ha02996 : a02996.IsHomogeneous 30 := by
  unfold a02996
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02995.pow 1)))

@[irreducible]
def a02997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00130 ^ 1)
theorem ha02997 : a02997.IsHomogeneous 12 := by
  unfold a02997
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)))

@[irreducible]
def a02998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha02998 : a02998.IsHomogeneous 12 := by
  unfold a02998
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a02999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha02999 : a02999.IsHomogeneous 6 := by
  unfold a02999
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02997 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02999 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02998 ^ 1)
theorem ha03000 : a03000.IsHomogeneous 18 := by
  unfold a03000
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02997.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02999.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02998.pow 1)))

@[irreducible]
def a03001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha03001 : a03001.IsHomogeneous 12 := by
  unfold a03001
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a03002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha03002 : a03002.IsHomogeneous 12 := by
  unfold a03002
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a03003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02997 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03002 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a03001 ^ 1)
theorem ha03003 : a03003.IsHomogeneous 18 := by
  unfold a03003
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02997.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03002.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha03001.pow 1)))

@[irreducible]
def a03004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1)
theorem ha03004 : a03004.IsHomogeneous 18 := by
  unfold a03004
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a03005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02998 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03001 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03004 ^ 1)
theorem ha03005 : a03005.IsHomogeneous 18 := by
  unfold a03005
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02998.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03001.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03004.pow 1)))

@[irreducible]
def a03006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03000 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03003 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03005 ^ 1)
theorem ha03006 : a03006.IsHomogeneous 24 := by
  unfold a03006
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03000.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03003.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03005.pow 1)))

@[irreducible]
def a03007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1)
theorem ha03007 : a03007.IsHomogeneous 24 := by
  unfold a03007
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a03008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha03008 : a03008.IsHomogeneous 12 := by
  unfold a03008
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a03009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03007 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02998 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03008 ^ 1)
theorem ha03009 : a03009.IsHomogeneous 24 := by
  unfold a03009
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02998.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03008.pow 1)))

@[irreducible]
def a03010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha03010 : a03010.IsHomogeneous 12 := by
  unfold a03010
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a03011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03010 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02999 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03008 ^ 1)
theorem ha03011 : a03011.IsHomogeneous 18 := by
  unfold a03011
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03010.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02999.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03008.pow 1)))

@[irreducible]
def a03012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03000 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03009 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a03011 ^ 1)
theorem ha03012 : a03012.IsHomogeneous 24 := by
  unfold a03012
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03000.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha03011.pow 1)))

@[irreducible]
def a03013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00864 ^ 1)
theorem ha03013 : a03013.IsHomogeneous 24 := by
  unfold a03013
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03007 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03013 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a03004 ^ 1)
theorem ha03014 : a03014.IsHomogeneous 24 := by
  unfold a03014
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03013.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha03004.pow 1)))

@[irreducible]
def a03015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03005 ^ 1)
theorem ha03015 : a03015.IsHomogeneous 24 := by
  unfold a03015
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03005.pow 1)))

@[irreducible]
def a03016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03012 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03015 ^ 1)
theorem ha03016 : a03016.IsHomogeneous 24 := by
  unfold a03016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03012.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03015.pow 1)))

@[irreducible]
def a03017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01373 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03016 ^ 1)
theorem ha03017 : a03017.IsHomogeneous 30 := by
  unfold a03017
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03016.pow 1)))

@[irreducible]
def a03018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03017 ^ 1)
theorem ha03018 : a03018.IsHomogeneous 30 := by
  unfold a03018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02992.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03017.pow 1)))

@[irreducible]
def a03019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02993 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03018 ^ 1)
theorem ha03019 : a03019.IsHomogeneous 30 := by
  unfold a03019
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03018.pow 1)))

@[irreducible]
def a03020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03019 ^ 1)
theorem ha03020 : a03020.IsHomogeneous 30 := by
  unfold a03020
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02996.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03019.pow 1)))

@[irreducible]
def a03021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00513 ^ 1)
theorem ha03021 : a03021.IsHomogeneous 24 := by
  unfold a03021
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00513.pow 1)))

@[irreducible]
def a03022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00513 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01340 ^ 1)
theorem ha03022 : a03022.IsHomogeneous 24 := by
  unfold a03022
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00513.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01340.pow 1)))

@[irreducible]
def a03023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03021 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03022 ^ 1)
theorem ha03023 : a03023.IsHomogeneous 24 := by
  unfold a03023
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03022.pow 1)))

@[irreducible]
def a03024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a02007 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00864 ^ 1)
theorem ha03024 : a03024.IsHomogeneous 24 := by
  unfold a03024
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03021 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a03024 ^ 1)
theorem ha03025 : a03025.IsHomogeneous 24 := by
  unfold a03025
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha03024.pow 1)))

@[irreducible]
def a03026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03025 ^ 1)
theorem ha03026 : a03026.IsHomogeneous 24 := by
  unfold a03026
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03025.pow 1)))

@[irreducible]
def a03027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02956 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01340 ^ 1)
theorem ha03027 : a03027.IsHomogeneous 24 := by
  unfold a03027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02956.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01340.pow 1)))

@[irreducible]
def a03028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03022 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a03027 ^ 1)
theorem ha03028 : a03028.IsHomogeneous 24 := by
  unfold a03028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03022.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha03027.pow 1)))

@[irreducible]
def a03029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03023 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03028 ^ 1)
theorem ha03029 : a03029.IsHomogeneous 24 := by
  unfold a03029
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03028.pow 1)))

@[irreducible]
def a03030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03029 ^ 1)
theorem ha03030 : a03030.IsHomogeneous 24 := by
  unfold a03030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03029.pow 1)))

@[irreducible]
def a03031 : Poly := (C ((-1 : ℂ) / (32 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a03020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a03030 ^ 1)
theorem ha03031 : a03031.IsHomogeneous 43 := by
  unfold a03031
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03020.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03030.pow 1)))

@[irreducible]
def a03032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00155 ^ 1)
theorem ha03032 : a03032.IsHomogeneous 24 := by
  unfold a03032
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a03033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00506 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha03033 : a03033.IsHomogeneous 24 := by
  unfold a03033
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1)
theorem ha03034 : a03034.IsHomogeneous 18 := by
  unfold a03034
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a03035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03032 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a03033 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03034 ^ 1)
theorem ha03035 : a03035.IsHomogeneous 24 := by
  unfold a03035
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha03033.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03034.pow 1)))

@[irreducible]
def a03036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00520 ^ 1)
theorem ha03036 : a03036.IsHomogeneous 12 := by
  unfold a03036
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00520.pow 1)))

@[irreducible]
def a03037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00520 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00520 ^ 1)
theorem ha03037 : a03037.IsHomogeneous 24 := by
  unfold a03037
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a03038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03032 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03037 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03036 ^ 1)
theorem ha03038 : a03038.IsHomogeneous 24 := by
  unfold a03038
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03037.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03036.pow 1)))

@[irreducible]
def a03039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha03039 : a03039.IsHomogeneous 12 := by
  unfold a03039
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a03040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03034 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03036 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03039 ^ 1)
theorem ha03040 : a03040.IsHomogeneous 18 := by
  unfold a03040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03034.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03036.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03039.pow 1)))

@[irreducible]
def a03041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03038 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03040 ^ 1)
theorem ha03041 : a03041.IsHomogeneous 24 := by
  unfold a03041
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03035.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03038.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03040.pow 1)))

@[irreducible]
def a03042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha03042 : a03042.IsHomogeneous 30 := by
  unfold a03042
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a01356 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00520 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00520 ^ 1)
theorem ha03043 : a03043.IsHomogeneous 30 := by
  unfold a03043
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a03044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03042 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a03043 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03032 ^ 1)
theorem ha03044 : a03044.IsHomogeneous 30 := by
  unfold a03044
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha03043.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03032.pow 1)))

@[irreducible]
def a03045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a01327 ^ 1)
theorem ha03045 : a03045.IsHomogeneous 24 := by
  unfold a03045
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03042 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03045 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03033 ^ 1)
theorem ha03046 : a03046.IsHomogeneous 30 := by
  unfold a03046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03045.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03033.pow 1)))

@[irreducible]
def a03047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03046 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03035 ^ 1)
theorem ha03047 : a03047.IsHomogeneous 30 := by
  unfold a03047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03046.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03035.pow 1)))

@[irreducible]
def a03048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01356 ^ 1)
theorem ha03048 : a03048.IsHomogeneous 30 := by
  unfold a03048
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a03049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03048 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03037 ^ 1)
theorem ha03049 : a03049.IsHomogeneous 30 := by
  unfold a03049
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03043.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03048.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03037.pow 1)))

@[irreducible]
def a03050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03044 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a03049 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03038 ^ 1)
theorem ha03050 : a03050.IsHomogeneous 30 := by
  unfold a03050
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha03049.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03038.pow 1)))

@[irreducible]
def a03051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03047 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03050 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03041 ^ 1)
theorem ha03051 : a03051.IsHomogeneous 30 := by
  unfold a03051
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03047.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03050.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03041.pow 1)))

@[irreducible]
def a03052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1)
theorem ha03052 : a03052.IsHomogeneous 24 := by
  unfold a03052
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00316 ^ 1)
theorem ha03053 : a03053.IsHomogeneous 24 := by
  unfold a03053
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a03054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00168 ^ 1)
theorem ha03054 : a03054.IsHomogeneous 12 := by
  unfold a03054
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00316.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00168.pow 1)))

@[irreducible]
def a03055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03052 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03053 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03054 ^ 1)
theorem ha03055 : a03055.IsHomogeneous 24 := by
  unfold a03055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03052.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03053.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03054.pow 1)))

@[irreducible]
def a03056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00547 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00168 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00168 ^ 1)
theorem ha03056 : a03056.IsHomogeneous 18 := by
  unfold a03056
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00547 ^ 1)
theorem ha03057 : a03057.IsHomogeneous 24 := by
  unfold a03057
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03052 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03057 ^ 1) + (C ((7 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03056 ^ 1)
theorem ha03058 : a03058.IsHomogeneous 24 := by
  unfold a03058
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03052.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03057.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03056.pow 1)))

@[irreducible]
def a03059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00037 ^ 1)
theorem ha03059 : a03059.IsHomogeneous 12 := by
  unfold a03059
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00037.pow 1)))

@[irreducible]
def a03060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03056 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a03059 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03054 ^ 1)
theorem ha03060 : a03060.IsHomogeneous 18 := by
  unfold a03060
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03056.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha03059.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03054.pow 1)))

@[irreducible]
def a03061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03055 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03058 ^ 1) + (C ((7 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03060 ^ 1)
theorem ha03061 : a03061.IsHomogeneous 24 := by
  unfold a03061
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03058.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03060.pow 1)))

@[irreducible]
def a03062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00547 ^ 1)
theorem ha03062 : a03062.IsHomogeneous 30 := by
  unfold a03062
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00547 ^ 1)
theorem ha03063 : a03063.IsHomogeneous 30 := by
  unfold a03063
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03062 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03052 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03063 ^ 1)
theorem ha03064 : a03064.IsHomogeneous 30 := by
  unfold a03064
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03062.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03052.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03063.pow 1)))

@[irreducible]
def a03065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00864 ^ 1)
theorem ha03065 : a03065.IsHomogeneous 30 := by
  unfold a03065
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03062 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03065 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03053 ^ 1)
theorem ha03066 : a03066.IsHomogeneous 30 := by
  unfold a03066
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03062.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03065.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03053.pow 1)))

@[irreducible]
def a03067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03064 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03066 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03055 ^ 1)
theorem ha03067 : a03067.IsHomogeneous 30 := by
  unfold a03067
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03064.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03066.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03055.pow 1)))

@[irreducible]
def a03068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha03068 : a03068.IsHomogeneous 12 := by
  unfold a03068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a03069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha03069 : a03069.IsHomogeneous 12 := by
  unfold a03069
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a03070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03068 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03069 ^ 1)
theorem ha03070 : a03070.IsHomogeneous 12 := by
  unfold a03070
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03068.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03069.pow 1)))

@[irreducible]
def a03071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1)
theorem ha03071 : a03071.IsHomogeneous 6 := by
  unfold a03071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)))

end CycleQ2Concrete
