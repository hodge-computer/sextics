import Proposal.CurrentAtoms022

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a07680 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07676 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a07679 ^ 1)
theorem ha07680 : a07680.IsHomogeneous 271 := by
  unfold a07680
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07676.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha07679.pow 1)))

@[irreducible]
def a07681 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07680 ^ 1)
theorem ha07681 : a07681.IsHomogeneous 271 := by
  unfold a07681
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07680.pow 1)))

@[irreducible]
def a07682 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01207 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1)
theorem ha07682 : a07682.IsHomogeneous 39 := by
  unfold a07682
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a07683 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha07683 : a07683.IsHomogeneous 33 := by
  unfold a07683
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07684 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha07684 : a07684.IsHomogeneous 33 := by
  unfold a07684
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a07685 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07684 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07682 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07683 ^ 1)
theorem ha07685 : a07685.IsHomogeneous 39 := by
  unfold a07685
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07684.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07682.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07683.pow 1)))

@[irreducible]
def a07686 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01207 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1)
theorem ha07686 : a07686.IsHomogeneous 42 := by
  unfold a07686
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01207.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a07687 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01207 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1)
theorem ha07687 : a07687.IsHomogeneous 42 := by
  unfold a07687
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a07688 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07686 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a07687 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07682 ^ 1)
theorem ha07688 : a07688.IsHomogeneous 48 := by
  unfold a07688
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07686.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha07687.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07682.pow 1)))

@[irreducible]
def a07689 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00042 ^ 1)
theorem ha07689 : a07689.IsHomogeneous 36 := by
  unfold a07689
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a07690 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07686 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07684 ^ 1)
theorem ha07690 : a07690.IsHomogeneous 42 := by
  unfold a07690
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07689.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07686.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07684.pow 1)))

@[irreducible]
def a07691 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07690 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07688 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07685 ^ 1)
theorem ha07691 : a07691.IsHomogeneous 48 := by
  unfold a07691
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07690.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07688.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07685.pow 1)))

@[irreducible]
def a07692 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a00865 ^ 1)
theorem ha07692 : a07692.IsHomogeneous 39 := by
  unfold a07692
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07693 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a02710 ^ 1)
theorem ha07693 : a07693.IsHomogeneous 39 := by
  unfold a07693
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a07694 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07682 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a07693 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07692 ^ 1)
theorem ha07694 : a07694.IsHomogeneous 45 := by
  unfold a07694
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07682.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha07693.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07692.pow 1)))

@[irreducible]
def a07695 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha07695 : a07695.IsHomogeneous 33 := by
  unfold a07695
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07696 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07692 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07695 ^ 1)
theorem ha07696 : a07696.IsHomogeneous 39 := by
  unfold a07696
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07692.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07695.pow 1)))

@[irreducible]
def a07697 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07685 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07694 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07696 ^ 1)
theorem ha07697 : a07697.IsHomogeneous 45 := by
  unfold a07697
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07685.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07694.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07696.pow 1)))

@[irreducible]
def a07698 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a05389 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02710 ^ 1)
theorem ha07698 : a07698.IsHomogeneous 42 := by
  unfold a07698
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha05389.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a07699 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07687 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07698 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07693 ^ 1)
theorem ha07699 : a07699.IsHomogeneous 42 := by
  unfold a07699
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07687.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07698.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07693.pow 1)))

@[irreducible]
def a07700 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07688 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a07699 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07694 ^ 1)
theorem ha07700 : a07700.IsHomogeneous 48 := by
  unfold a07700
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07688.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha07699.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07694.pow 1)))

@[irreducible]
def a07701 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07700 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07697 ^ 1)
theorem ha07701 : a07701.IsHomogeneous 48 := by
  unfold a07701
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07691.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07700.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07697.pow 1)))

@[irreducible]
def a07702 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha07702 : a07702.IsHomogeneous 36 := by
  unfold a07702
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07703 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1)
theorem ha07703 : a07703.IsHomogeneous 42 := by
  unfold a07703
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a07704 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha07704 : a07704.IsHomogeneous 36 := by
  unfold a07704
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a07705 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07702 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a07704 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a07703 ^ 1)
theorem ha07705 : a07705.IsHomogeneous 42 := by
  unfold a07705
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha07704.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha07703.pow 1)))

@[irreducible]
def a07706 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00809 ^ 1)
theorem ha07706 : a07706.IsHomogeneous 33 := by
  unfold a07706
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00809.pow 1)))

@[irreducible]
def a07707 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00298 ^ 1)
theorem ha07707 : a07707.IsHomogeneous 36 := by
  unfold a07707
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00298.pow 1)))

@[irreducible]
def a07708 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07707 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07706 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07702 ^ 1)
theorem ha07708 : a07708.IsHomogeneous 42 := by
  unfold a07708
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07707.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07706.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07702.pow 1)))

@[irreducible]
def a07709 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha07709 : a07709.IsHomogeneous 36 := by
  unfold a07709
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a07710 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07707 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a07709 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a07704 ^ 1)
theorem ha07710 : a07710.IsHomogeneous 42 := by
  unfold a07710
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07707.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha07709.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha07704.pow 1)))

@[irreducible]
def a07711 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07708 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07710 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07705 ^ 1)
theorem ha07711 : a07711.IsHomogeneous 48 := by
  unfold a07711
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07708.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07710.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07705.pow 1)))

@[irreducible]
def a07712 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00864 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00316 ^ 1 * a00809 ^ 1)
theorem ha07712 : a07712.IsHomogeneous 42 := by
  unfold a07712
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07713 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00809 ^ 1)
theorem ha07713 : a07713.IsHomogeneous 33 := by
  unfold a07713
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a07714 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07712 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07713 ^ 1)
theorem ha07714 : a07714.IsHomogeneous 42 := by
  unfold a07714
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07712.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07713.pow 1)))

@[irreducible]
def a07715 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a02007 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00864 ^ 1)
theorem ha07715 : a07715.IsHomogeneous 42 := by
  unfold a07715
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha02007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a07716 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07715 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a07712 ^ 1)
theorem ha07716 : a07716.IsHomogeneous 42 := by
  unfold a07716
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07703.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07715.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha07712.pow 1)))

@[irreducible]
def a07717 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07705 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07714 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a07716 ^ 1)
theorem ha07717 : a07717.IsHomogeneous 42 := by
  unfold a07717
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07705.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07714.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha07716.pow 1)))

@[irreducible]
def a07718 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a03890 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01896 ^ 1)
theorem ha07718 : a07718.IsHomogeneous 33 := by
  unfold a07718
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01896.pow 1)))

@[irreducible]
def a07719 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07706 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07718 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07713 ^ 1)
theorem ha07719 : a07719.IsHomogeneous 39 := by
  unfold a07719
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07718.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07713.pow 1)))

@[irreducible]
def a07720 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07708 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07719 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07714 ^ 1)
theorem ha07720 : a07720.IsHomogeneous 48 := by
  unfold a07720
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07708.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07719.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07714.pow 1)))

@[irreducible]
def a07721 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07711 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07720 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07717 ^ 1)
theorem ha07721 : a07721.IsHomogeneous 48 := by
  unfold a07721
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07711.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07720.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07717.pow 1)))

@[irreducible]
def a07722 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07701 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a07721 ^ 1)
theorem ha07722 : a07722.IsHomogeneous 48 := by
  unfold a07722
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07701.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha07721.pow 1)))

@[irreducible]
def a07723 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07722 ^ 1)
theorem ha07723 : a07723.IsHomogeneous 48 := by
  unfold a07723
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07701.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07722.pow 1)))

@[irreducible]
def a07724 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07723 ^ 1)
theorem ha07724 : a07724.IsHomogeneous 48 := by
  unfold a07724
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07701.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07723.pow 1)))

@[irreducible]
def a07725 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07721 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07722 ^ 1)
theorem ha07725 : a07725.IsHomogeneous 48 := by
  unfold a07725
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07722.pow 1)))

@[irreducible]
def a07726 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07723 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a07725 ^ 1)
theorem ha07726 : a07726.IsHomogeneous 48 := by
  unfold a07726
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07723.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha07725.pow 1)))

@[irreducible]
def a07727 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07724 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07726 ^ 1)
theorem ha07727 : a07727.IsHomogeneous 48 := by
  unfold a07727
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07726.pow 1)))

@[irreducible]
def a07728 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07724 ^ 1)
theorem ha07728 : a07728.IsHomogeneous 48 := by
  unfold a07728
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07701.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07724.pow 1)))

@[irreducible]
def a07729 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07728 ^ 1)
theorem ha07729 : a07729.IsHomogeneous 48 := by
  unfold a07729
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07728.pow 1)))

@[irreducible]
def a07730 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07725 ^ 1)
theorem ha07730 : a07730.IsHomogeneous 48 := by
  unfold a07730
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07725.pow 1)))

@[irreducible]
def a07731 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07726 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a07730 ^ 1)
theorem ha07731 : a07731.IsHomogeneous 48 := by
  unfold a07731
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07726.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha07730.pow 1)))

@[irreducible]
def a07732 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07727 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07731 ^ 1)
theorem ha07732 : a07732.IsHomogeneous 48 := by
  unfold a07732
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07727.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07731.pow 1)))

@[irreducible]
def a07733 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07729 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07732 ^ 1)
theorem ha07733 : a07733.IsHomogeneous 48 := by
  unfold a07733
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07729.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07732.pow 1)))

@[irreducible]
def a07734 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06282 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a06702 ^ 1)
theorem ha07734 : a07734.IsHomogeneous 48 := by
  unfold a07734
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha06702.pow 1)))

@[irreducible]
def a07735 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06702 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07734 ^ 1)
theorem ha07735 : a07735.IsHomogeneous 48 := by
  unfold a07735
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07734.pow 1)))

@[irreducible]
def a07736 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07734 ^ 1)
theorem ha07736 : a07736.IsHomogeneous 48 := by
  unfold a07736
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07734.pow 1)))

@[irreducible]
def a07737 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07735 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07736 ^ 1)
theorem ha07737 : a07737.IsHomogeneous 48 := by
  unfold a07737
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07735.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07736.pow 1)))

@[irreducible]
def a07738 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07736 ^ 1)
theorem ha07738 : a07738.IsHomogeneous 48 := by
  unfold a07738
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07736.pow 1)))

@[irreducible]
def a07739 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07737 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07738 ^ 1)
theorem ha07739 : a07739.IsHomogeneous 48 := by
  unfold a07739
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07737.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07738.pow 1)))

@[irreducible]
def a07740 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07735 ^ 1)
theorem ha07740 : a07740.IsHomogeneous 48 := by
  unfold a07740
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07735.pow 1)))

@[irreducible]
def a07741 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07737 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07740 ^ 1)
theorem ha07741 : a07741.IsHomogeneous 48 := by
  unfold a07741
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07737.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07740.pow 1)))

@[irreducible]
def a07742 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07741 ^ 1)
theorem ha07742 : a07742.IsHomogeneous 48 := by
  unfold a07742
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07741.pow 1)))

@[irreducible]
def a07743 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07738 ^ 1)
theorem ha07743 : a07743.IsHomogeneous 48 := by
  unfold a07743
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07738.pow 1)))

@[irreducible]
def a07744 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07739 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07743 ^ 1)
theorem ha07744 : a07744.IsHomogeneous 48 := by
  unfold a07744
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07739.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07743.pow 1)))

@[irreducible]
def a07745 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07742 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07744 ^ 1)
theorem ha07745 : a07745.IsHomogeneous 48 := by
  unfold a07745
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07742.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07744.pow 1)))

@[irreducible]
def a07746 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06345 ^ 1)
theorem ha07746 : a07746.IsHomogeneous 48 := by
  unfold a07746
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)))

@[irreducible]
def a07747 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07746 ^ 1)
theorem ha07747 : a07747.IsHomogeneous 48 := by
  unfold a07747
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07746.pow 1)))

@[irreducible]
def a07748 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07746 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06345 ^ 1)
theorem ha07748 : a07748.IsHomogeneous 48 := by
  unfold a07748
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07746.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)))

@[irreducible]
def a07749 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07747 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07748 ^ 1)
theorem ha07749 : a07749.IsHomogeneous 48 := by
  unfold a07749
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07747.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07748.pow 1)))

@[irreducible]
def a07750 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07747 ^ 1)
theorem ha07750 : a07750.IsHomogeneous 48 := by
  unfold a07750
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07747.pow 1)))

@[irreducible]
def a07751 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07750 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07749 ^ 1)
theorem ha07751 : a07751.IsHomogeneous 48 := by
  unfold a07751
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07750.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07749.pow 1)))

@[irreducible]
def a07752 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06345 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07746 ^ 1)
theorem ha07752 : a07752.IsHomogeneous 48 := by
  unfold a07752
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07746.pow 1)))

@[irreducible]
def a07753 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07747 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07752 ^ 1)
theorem ha07753 : a07753.IsHomogeneous 48 := by
  unfold a07753
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07747.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07752.pow 1)))

@[irreducible]
def a07754 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06345 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07752 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07748 ^ 1)
theorem ha07754 : a07754.IsHomogeneous 48 := by
  unfold a07754
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07752.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07748.pow 1)))

@[irreducible]
def a07755 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07749 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07753 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07754 ^ 1)
theorem ha07755 : a07755.IsHomogeneous 48 := by
  unfold a07755
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07753.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07754.pow 1)))

@[irreducible]
def a07756 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07750 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07753 ^ 1)
theorem ha07756 : a07756.IsHomogeneous 48 := by
  unfold a07756
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07750.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07753.pow 1)))

@[irreducible]
def a07757 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07751 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07756 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07755 ^ 1)
theorem ha07757 : a07757.IsHomogeneous 48 := by
  unfold a07757
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07751.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07756.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07755.pow 1)))

@[irreducible]
def a07758 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06345 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07752 ^ 1)
theorem ha07758 : a07758.IsHomogeneous 48 := by
  unfold a07758
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07752.pow 1)))

@[irreducible]
def a07759 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07753 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07758 ^ 1)
theorem ha07759 : a07759.IsHomogeneous 48 := by
  unfold a07759
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07753.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07758.pow 1)))

@[irreducible]
def a07760 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06345 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07758 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07754 ^ 1)
theorem ha07760 : a07760.IsHomogeneous 48 := by
  unfold a07760
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07758.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07754.pow 1)))

@[irreducible]
def a07761 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07755 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07759 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a07760 ^ 1)
theorem ha07761 : a07761.IsHomogeneous 48 := by
  unfold a07761
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07755.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07759.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha07760.pow 1)))

@[irreducible]
def a07762 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07756 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07759 ^ 1)
theorem ha07762 : a07762.IsHomogeneous 48 := by
  unfold a07762
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07759.pow 1)))

@[irreducible]
def a07763 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07757 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07762 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07761 ^ 1)
theorem ha07763 : a07763.IsHomogeneous 48 := by
  unfold a07763
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07757.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07762.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07761.pow 1)))

@[irreducible]
def a07764 : Poly := (C ((-35 : ℂ) / (9 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06404 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a07763 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07733 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07745 ^ 1)
theorem ha07764 : a07764.IsHomogeneous 48 := by
  unfold a07764
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-35 : ℂ) / (9 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07763.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07733.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07745.pow 1)))

@[irreducible]
def a07765 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00327 ^ 1 * a01678 ^ 1)
theorem ha07765 : a07765.IsHomogeneous 197 := by
  unfold a07765
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha00880.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a07766 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02041 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a00880 ^ 1)
theorem ha07766 : a07766.IsHomogeneous 235 := by
  unfold a07766
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02041.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a07767 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07766 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a07765 ^ 1)
theorem ha07767 : a07767.IsHomogeneous 235 := by
  unfold a07767
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07766.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha07765.pow 1)))

@[irreducible]
def a07768 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a01678 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00134 ^ 1 * a03534 ^ 1)
theorem ha07768 : a07768.IsHomogeneous 155 := by
  unfold a07768
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha01678.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a07769 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07765 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07768 ^ 1)
theorem ha07769 : a07769.IsHomogeneous 197 := by
  unfold a07769
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07765.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07768.pow 1)))

@[irreducible]
def a07770 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07767 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a07769 ^ 1)
theorem ha07770 : a07770.IsHomogeneous 235 := by
  unfold a07770
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07767.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha07769.pow 1)))

@[irreducible]
def a07771 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04148 ^ 1)
theorem ha07771 : a07771.IsHomogeneous 271 := by
  unfold a07771
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04148.pow 1)))

@[irreducible]
def a07772 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a07766 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07771 ^ 1)
theorem ha07772 : a07772.IsHomogeneous 271 := by
  unfold a07772
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha07766.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07771.pow 1)))

@[irreducible]
def a07773 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a07767 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07772 ^ 1)
theorem ha07773 : a07773.IsHomogeneous 271 := by
  unfold a07773
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha07767.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07772.pow 1)))

@[irreducible]
def a07774 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a07770 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07773 ^ 1)
theorem ha07774 : a07774.IsHomogeneous 271 := by
  unfold a07774
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha07770.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07773.pow 1)))

@[irreducible]
def a07775 : Poly := (C ((-1 : ℂ) / (116640 : ℂ)) * a00001 ^ 5 * a00003 ^ 6 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 5 * a00100 ^ 5 * a07764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07774 ^ 1)
theorem ha07775 : a07775.IsHomogeneous 271 := by
  unfold a07775
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (116640 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 6)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 5)).mul (ha00100.pow 5)).mul (ha07764.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07774.pow 1)))

@[irreducible]
def a07776 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04229 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a07775 ^ 1)
theorem ha07776 : a07776.IsHomogeneous 271 := by
  unfold a07776
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04229.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha07775.pow 1)))

@[irreducible]
def a07777 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07677 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07776 ^ 1)
theorem ha07777 : a07777.IsHomogeneous 271 := by
  unfold a07777
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07677.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07776.pow 1)))

@[irreducible]
def a07778 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07678 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a07777 ^ 1)
theorem ha07778 : a07778.IsHomogeneous 271 := by
  unfold a07778
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07678.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha07777.pow 1)))

@[irreducible]
def a07779 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07681 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07778 ^ 1)
theorem ha07779 : a07779.IsHomogeneous 271 := by
  unfold a07779
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07681.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07778.pow 1)))

@[irreducible]
def a07780 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a07779 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a04232 ^ 1)
theorem ha07780 : a07780.IsHomogeneous 829 := by
  unfold a07780
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha07779.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a07781 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07674 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a07780 ^ 1)
theorem ha07781 : a07781.IsHomogeneous 1276 := by
  unfold a07781
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07674.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha07780.pow 1)))

@[irreducible]
def a07782 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07675 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07781 ^ 1)
theorem ha07782 : a07782.IsHomogeneous 1693 := by
  unfold a07782
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07675.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07781.pow 1)))

@[irreducible]
def a07783 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a04155 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a02046 ^ 1)
theorem ha07783 : a07783.IsHomogeneous 2110 := by
  unfold a07783
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha04155.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha02046.pow 1)))

@[irreducible]
def a07784 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07783 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07673 ^ 1)
theorem ha07784 : a07784.IsHomogeneous 2110 := by
  unfold a07784
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07783.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07673.pow 1)))

@[irreducible]
def a07785 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07784 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07675 ^ 1)
theorem ha07785 : a07785.IsHomogeneous 2110 := by
  unfold a07785
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07784.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07675.pow 1)))

@[irreducible]
def a07786 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07785 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07782 ^ 1)
theorem ha07786 : a07786.IsHomogeneous 2110 := by
  unfold a07786
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07785.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07782.pow 1)))

@[irreducible]
def a07787 : Poly := (C ((-9 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a07672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07786 ^ 1)
theorem ha07787 : a07787.IsHomogeneous 2527 := by
  unfold a07787
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha07672.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07786.pow 1)))

@[irreducible]
def a07788 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a07787 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 6 * a05704 ^ 1)
theorem ha07788 : a07788.IsHomogeneous 2555 := by
  unfold a07788
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha07787.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 6)).mul (ha05704.pow 1)))

@[irreducible]
def a07789 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a04239 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07788 ^ 1)
theorem ha07789 : a07789.IsHomogeneous 2555 := by
  unfold a07789
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha04239.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07788.pow 1)))

@[irreducible]
def a07790 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05303 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07789 ^ 1)
theorem ha07790 : a07790.IsHomogeneous 2555 := by
  unfold a07790
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05303.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07789.pow 1)))

@[irreducible]
def a07791 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05305 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07790 ^ 1)
theorem ha07791 : a07791.IsHomogeneous 2555 := by
  unfold a07791
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05305.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07790.pow 1)))

@[irreducible]
def a07792 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00934 ^ 1 * a02043 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00364 ^ 1 * a04151 ^ 1)
theorem ha07792 : a07792.IsHomogeneous 1484 := by
  unfold a07792
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00934.pow 1)).mul (ha02043.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha04151.pow 1)))

@[irreducible]
def a07793 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05304 ^ 1)
theorem ha07793 : a07793.IsHomogeneous 1841 := by
  unfold a07793
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05304.pow 1)))

@[irreducible]
def a07794 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07793 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05305 ^ 1)
theorem ha07794 : a07794.IsHomogeneous 2198 := by
  unfold a07794
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07793.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05305.pow 1)))

@[irreducible]
def a07795 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07794 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07791 ^ 1)
theorem ha07795 : a07795.IsHomogeneous 2555 := by
  unfold a07795
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07794.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07791.pow 1)))

@[irreducible]
def a07796 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00935 ^ 1 * a02104 ^ 1)
theorem ha07796 : a07796.IsHomogeneous 1782 := by
  unfold a07796
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00935.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a07797 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a04232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a02104 ^ 1)
theorem ha07797 : a07797.IsHomogeneous 1365 := by
  unfold a07797
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha04232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a07798 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07796 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07797 ^ 1)
theorem ha07798 : a07798.IsHomogeneous 1782 := by
  unfold a07798
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07796.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07797.pow 1)))

@[irreducible]
def a07799 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a04244 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a02112 ^ 1)
theorem ha07799 : a07799.IsHomogeneous 2199 := by
  unfold a07799
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha04244.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha02112.pow 1)))

@[irreducible]
def a07800 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07799 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07796 ^ 1)
theorem ha07800 : a07800.IsHomogeneous 2199 := by
  unfold a07800
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07799.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07796.pow 1)))

@[irreducible]
def a07801 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07800 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07798 ^ 1)
theorem ha07801 : a07801.IsHomogeneous 2199 := by
  unfold a07801
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07800.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07798.pow 1)))

@[irreducible]
def a07802 : Poly := (C ((-81 : ℂ) / (250 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a07795 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07801 ^ 1)
theorem ha07802 : a07802.IsHomogeneous 2616 := by
  unfold a07802
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (250 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha07795.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07801.pow 1)))

@[irreducible]
def a07803 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a07802 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a05302 ^ 1)
theorem ha07803 : a07803.IsHomogeneous 2623 := by
  unfold a07803
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha07802.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha05302.pow 1)))

@[irreducible]
def a07804 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a04249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07803 ^ 1)
theorem ha07804 : a07804.IsHomogeneous 2623 := by
  unfold a07804
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha04249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07803.pow 1)))

@[irreducible]
def a07805 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04830 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07804 ^ 1)
theorem ha07805 : a07805.IsHomogeneous 2623 := by
  unfold a07805
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04830.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07804.pow 1)))

@[irreducible]
def a07806 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a02115 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00937 ^ 1 * a02043 ^ 1)
theorem ha07806 : a07806.IsHomogeneous 1909 := by
  unfold a07806
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha02115.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00937.pow 1)).mul (ha02043.pow 1)))

@[irreducible]
def a07807 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07806 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04830 ^ 1)
theorem ha07807 : a07807.IsHomogeneous 2266 := by
  unfold a07807
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07806.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04830.pow 1)))

@[irreducible]
def a07808 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07807 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07805 ^ 1)
theorem ha07808 : a07808.IsHomogeneous 2623 := by
  unfold a07808
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07807.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07805.pow 1)))

@[irreducible]
def a07809 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00937 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a02116 ^ 1)
theorem ha07809 : a07809.IsHomogeneous 1850 := by
  unfold a07809
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00937.pow 1)).mul (ha02104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a07810 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a04252 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a02116 ^ 1)
theorem ha07810 : a07810.IsHomogeneous 2267 := by
  unfold a07810
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha04252.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a07811 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07810 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07809 ^ 1)
theorem ha07811 : a07811.IsHomogeneous 2267 := by
  unfold a07811
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07810.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07809.pow 1)))

@[irreducible]
def a07812 : Poly := (C ((-27 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a07808 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07811 ^ 1)
theorem ha07812 : a07812.IsHomogeneous 2684 := by
  unfold a07812
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha07808.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07811.pow 1)))

@[irreducible]
def a07813 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a04829 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a07812 ^ 1)
theorem ha07813 : a07813.IsHomogeneous 2696 := by
  unfold a07813
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha04829.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha07812.pow 1)))

@[irreducible]
def a07814 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a04255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07813 ^ 1)
theorem ha07814 : a07814.IsHomogeneous 2696 := by
  unfold a07814
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha04255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07813.pow 1)))

@[irreducible]
def a07815 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a02118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04255 ^ 1)
theorem ha07815 : a07815.IsHomogeneous 2339 := by
  unfold a07815
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha02118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04255.pow 1)))

@[irreducible]
def a07816 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07815 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07814 ^ 1)
theorem ha07816 : a07816.IsHomogeneous 2696 := by
  unfold a07816
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07815.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07814.pow 1)))

@[irreducible]
def a07817 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a04256 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a02118 ^ 1)
theorem ha07817 : a07817.IsHomogeneous 2340 := by
  unfold a07817
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha04256.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha02118.pow 1)))

@[irreducible]
def a07818 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a07817 ^ 1) + (C ((3 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a07816 ^ 1)
theorem ha07818 : a07818.IsHomogeneous 2757 := by
  unfold a07818
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha07817.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha07816.pow 1)))

@[irreducible]
def a07819 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07818 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a04505 ^ 1)
theorem ha07819 : a07819.IsHomogeneous 2763 := by
  unfold a07819
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07818.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha04505.pow 1)))

@[irreducible]
def a07820 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a04258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07819 ^ 1)
theorem ha07820 : a07820.IsHomogeneous 2763 := by
  unfold a07820
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha04258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07819.pow 1)))

@[irreducible]
def a07821 : Poly := (C ((-27 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a07820 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00362 ^ 1 * a04258 ^ 1)
theorem ha07821 : a07821.IsHomogeneous 2824 := by
  unfold a07821
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha07820.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00362.pow 1)).mul (ha04258.pow 1)))

@[irreducible]
def a07822 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a07821 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a04332 ^ 1)
theorem ha07822 : a07822.IsHomogeneous 2829 := by
  unfold a07822
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07821.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha04332.pow 1)))

@[irreducible]
def a07823 : Poly := (C ((-12 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00100 ^ 2 * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 4 * a02118 ^ 1) + (C ((-9 : ℂ) / (160 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 3 * a00100 ^ 3 * a00101 ^ 3 * a00103 ^ 3 * a00105 ^ 3 * a00123 ^ 3 * a00124 ^ 3 * a00134 ^ 6 * a00937 ^ 1) + (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 2 * a00002 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07822 ^ 1) + (C ((9 : ℂ) / (200 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 2 * a00004 ^ 3 * a00005 ^ 2 * a00012 ^ 3 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 4 * a00101 ^ 4 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 4 * a00124 ^ 4 * a00126 ^ 1 * a00134 ^ 8 * a00364 ^ 1) + (C ((27 : ℂ) / (500 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 4 * a00004 ^ 3 * a00005 ^ 3 * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 7 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00117 ^ 1 * a00123 ^ 5 * a00124 ^ 5 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a00134 ^ 10)
theorem ha07823 : a07823.IsHomogeneous 2829 := by
  unfold a07823
  exact (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 4)).mul (ha02118.pow 1)).add (((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (160 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha00101.pow 3)).mul (ha00103.pow 3)).mul (ha00105.pow 3)).mul (ha00123.pow 3)).mul (ha00124.pow 3)).mul (ha00134.pow 6)).mul (ha00937.pow 1))).add (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04258.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07822.pow 1))).add ((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (200 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00004.pow 3)).mul (ha00005.pow 2)).mul (ha00012.pow 3)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha00101.pow 4)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 4)).mul (ha00124.pow 4)).mul (ha00126.pow 1)).mul (ha00134.pow 8)).mul (ha00364.pow 1))).add (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (500 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 7)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00117.pow 1)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00134.pow 10)))

@[irreducible]
def a07824 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00015 ^ 1 * a00019 ^ 1)
theorem ha07824 : a07824.IsHomogeneous 24 := by
  unfold a07824
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00015.pow 1)).mul (ha00019.pow 1)))

@[irreducible]
def a07825 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (1 : ℂ)) * a00021 ^ 1)
theorem ha07825 : a07825.IsHomogeneous 30 := by
  unfold a07825
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00014.pow 4)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00021.pow 1)))

@[irreducible]
def a07826 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00018 ^ 3 * a00033 ^ 1 * a00107 ^ 1 * a07823 ^ 1 * a07824 ^ 1) + (C ((729 : ℂ) / (125 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 2 * a00003 ^ 1 * a00014 ^ 11 * a00015 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 1 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07825 ^ 1)
theorem ha07826 : a07826.IsHomogeneous 3000 := by
  unfold a07826
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00018.pow 3)).mul (ha00033.pow 1)).mul (ha00107.pow 1)).mul (ha07823.pow 1)).mul (ha07824.pow 1)).add ((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00003.pow 1)).mul (ha00014.pow 11)).mul (ha00015.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 1)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07825.pow 1)))

@[irreducible]
def a07827 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 6) + (C ((1 : ℂ) / (2 : ℂ)) * a00001 ^ 6)
theorem ha07827 : a07827.IsHomogeneous 6 := by
  unfold a07827
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 6)))

@[irreducible]
def a07828 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a07827 ^ 1)
theorem ha07828 : a07828.IsHomogeneous 6 := by
  unfold a07828
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha07827.pow 1)))

@[irreducible]
def a07829 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07828 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00000 ^ 6)
theorem ha07829 : a07829.IsHomogeneous 6 := by
  unfold a07829
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07828.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)))

@[irreducible]
def a07830 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 5) + (C ((1 : ℂ) / (12 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1)
theorem ha07830 : a07830.IsHomogeneous 5 := by
  unfold a07830
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 5)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)))

@[irreducible]
def a07831 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a07830 ^ 1)
theorem ha07831 : a07831.IsHomogeneous 5 := by
  unfold a07831
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha07830.pow 1)))

@[irreducible]
def a07832 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1)
theorem ha07832 : a07832.IsHomogeneous 42 := by
  unfold a07832
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)))

@[irreducible]
def a07833 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a07832 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00032 ^ 1 * a00104 ^ 1)
theorem ha07833 : a07833.IsHomogeneous 48 := by
  unfold a07833
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha07832.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00032.pow 1)).mul (ha00104.pow 1)))

@[irreducible]
def a07834 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 1)
theorem ha07834 : a07834.IsHomogeneous 13 := by
  unfold a07834
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a07835 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00107 ^ 1 * a07834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00109 ^ 1)
theorem ha07835 : a07835.IsHomogeneous 30 := by
  unfold a07835
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00107.pow 1)).mul (ha07834.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00109.pow 1)))

@[irreducible]
def a07836 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((1 : ℂ) / (1 : ℂ)) * a00113 ^ 1)
theorem ha07836 : a07836.IsHomogeneous 15 := by
  unfold a07836
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00113.pow 1)))

@[irreducible]
def a07837 : Poly := (C ((-1 : ℂ) / (1296 : ℂ)) * a00005 ^ 3 * a00107 ^ 1 * a00109 ^ 1 * a07836 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a07835 ^ 1)
theorem ha07837 : a07837.IsHomogeneous 48 := by
  unfold a07837
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1296 : ℂ))).mul (ha00005.pow 3)).mul (ha00107.pow 1)).mul (ha00109.pow 1)).mul (ha07836.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha07835.pow 1)))

@[irreducible]
def a07838 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a07837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00112 ^ 1)
theorem ha07838 : a07838.IsHomogeneous 48 := by
  unfold a07838
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha07837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00112.pow 1)))

@[irreducible]
def a07839 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00116 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00107 ^ 1 * a00114 ^ 1)
theorem ha07839 : a07839.IsHomogeneous 46 := by
  unfold a07839
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00116.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00107.pow 1)).mul (ha00114.pow 1)))

@[irreducible]
def a07840 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00116 ^ 1)
theorem ha07840 : a07840.IsHomogeneous 46 := by
  unfold a07840
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07839.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00116.pow 1)))

@[irreducible]
def a07841 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00107 ^ 1 * a00114 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a07840 ^ 1)
theorem ha07841 : a07841.IsHomogeneous 46 := by
  unfold a07841
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha07840.pow 1)))

@[irreducible]
def a07842 : Poly := (C ((-864 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07838 ^ 1)
theorem ha07842 : a07842.IsHomogeneous 48 := by
  unfold a07842
  exact ((((isHomogeneous_C (σ := Fin 6) ((-864 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07841.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07838.pow 1)))

@[irreducible]
def a07843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07842 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a07833 ^ 1)
theorem ha07843 : a07843.IsHomogeneous 103 := by
  unfold a07843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07842.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha07833.pow 1)))

@[irreducible]
def a07844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00032 ^ 1)
theorem ha07844 : a07844.IsHomogeneous 25 := by
  unfold a07844
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a07845 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00025 ^ 2 * a07844 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a07832 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00032 ^ 1 * a00104 ^ 1)
theorem ha07845 : a07845.IsHomogeneous 54 := by
  unfold a07845
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00025.pow 2)).mul (ha07844.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha07832.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha00104.pow 1)))

@[irreducible]
def a07846 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1)
theorem ha07846 : a07846.IsHomogeneous 6 := by
  unfold a07846
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)))

@[irreducible]
def a07847 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a07846 ^ 1)
theorem ha07847 : a07847.IsHomogeneous 24 := by
  unfold a07847
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00017.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha07846.pow 1)))

@[irreducible]
def a07848 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00120 ^ 1 * a07845 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00118 ^ 1 * a07847 ^ 1)
theorem ha07848 : a07848.IsHomogeneous 87 := by
  unfold a07848
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00120.pow 1)).mul (ha07845.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00118.pow 1)).mul (ha07847.pow 1)))

@[irreducible]
def a07849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00032 ^ 1)
theorem ha07849 : a07849.IsHomogeneous 25 := by
  unfold a07849
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a07850 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00003 ^ 2 * a00025 ^ 1 * a07849 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00120 ^ 1)
theorem ha07850 : a07850.IsHomogeneous 37 := by
  unfold a07850
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha07849.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00120.pow 1)))

@[irreducible]
def a07851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a07850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a00121 ^ 1)
theorem ha07851 : a07851.IsHomogeneous 79 := by
  unfold a07851
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha07850.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha00121.pow 1)))

@[irreducible]
def a07852 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00120 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00058 ^ 1 * a00103 ^ 1)
theorem ha07852 : a07852.IsHomogeneous 73 := by
  unfold a07852
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00120.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00058.pow 1)).mul (ha00103.pow 1)))

@[irreducible]
def a07853 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00003 ^ 2 * a00004 ^ 1 * a00032 ^ 1 * a07852 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07848 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00025 ^ 1 * a07851 ^ 1)
theorem ha07853 : a07853.IsHomogeneous 87 := by
  unfold a07853
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00032.pow 1)).mul (ha07852.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07848.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00025.pow 1)).mul (ha07851.pow 1)))

@[irreducible]
def a07854 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a07853 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00004 ^ 1 * a00106 ^ 1 * a00120 ^ 1 * a00123 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00103 ^ 1 * a00123 ^ 1)
theorem ha07854 : a07854.IsHomogeneous 147 := by
  unfold a07854
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha07853.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00004.pow 1)).mul (ha00106.pow 1)).mul (ha00120.pow 1)).mul (ha00123.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)))

@[irreducible]
def a07855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a07843 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00105 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a07854 ^ 1)
theorem ha07855 : a07855.IsHomogeneous 242 := by
  unfold a07855
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07843.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha07854.pow 1)))

@[irreducible]
def a07856 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1)
theorem ha07856 : a07856.IsHomogeneous 24 := by
  unfold a07856
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)))

@[irreducible]
def a07857 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1)
theorem ha07857 : a07857.IsHomogeneous 24 := by
  unfold a07857
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)))

@[irreducible]
def a07858 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00009 ^ 1 * a00012 ^ 2 * a07857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 2 * a00102 ^ 1 * a00119 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1 * a07856 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 8 * a00001 ^ 4 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 4)
theorem ha07858 : a07858.IsHomogeneous 49 := by
  unfold a07858
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).mul (ha07857.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 2)).mul (ha00102.pow 1)).mul (ha00119.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha07856.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 4)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 4)))

@[irreducible]
def a07859 : Poly := (C ((-72 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00124 ^ 1 * a07833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00105 ^ 1 * a07858 ^ 1)
theorem ha07859 : a07859.IsHomogeneous 109 := by
  unfold a07859
  exact (((((isHomogeneous_C (σ := Fin 6) ((-72 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00124.pow 1)).mul (ha07833.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07858.pow 1)))

@[irreducible]
def a07860 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00105 ^ 1 * a00124 ^ 1 * a07853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00123 ^ 1 * a07859 ^ 1)
theorem ha07860 : a07860.IsHomogeneous 207 := by
  unfold a07860
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07853.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00123.pow 1)).mul (ha07859.pow 1)))

@[irreducible]
def a07861 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 2) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00025 ^ 1 * a00103 ^ 1 * a00104 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 3 * a00002 ^ 6 * a00003 ^ 3 * a00005 ^ 3 * a00104 ^ 3)
theorem ha07861 : a07861.IsHomogeneous 90 := by
  unfold a07861
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 2)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha00104.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 6)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00104.pow 3)))

@[irreducible]
def a07862 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00103 ^ 1 * a00105 ^ 1 * a07853 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00105 ^ 1 * a00120 ^ 1 * a00123 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a07833 ^ 1)
theorem ha07862 : a07862.IsHomogeneous 189 := by
  unfold a07862
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha07853.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00120.pow 1)).mul (ha00123.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07833.pow 1)))

@[irreducible]
def a07863 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00004 ^ 1 * a00123 ^ 2 * a07861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 6 * a00124 ^ 1 * a07862 ^ 1)
theorem ha07863 : a07863.IsHomogeneous 285 := by
  unfold a07863
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00004.pow 1)).mul (ha00123.pow 2)).mul (ha07861.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 6)).mul (ha00124.pow 1)).mul (ha07862.pow 1)))

@[irreducible]
def a07864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 6 * a00124 ^ 1 * a07855 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00014 ^ 6 * a00103 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a07860 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a07863 ^ 1)
theorem ha07864 : a07864.IsHomogeneous 338 := by
  unfold a07864
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 6)).mul (ha00124.pow 1)).mul (ha07855.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00014.pow 6)).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha07860.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha07863.pow 1)))

@[irreducible]
def a07865 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00014 ^ 1 * a01732 ^ 1)
theorem ha07865 : a07865.IsHomogeneous 22 := by
  unfold a07865
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha01732.pow 1)))

@[irreducible]
def a07866 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00002 ^ 4 * a00003 ^ 1 * a00012 ^ 1 * a00103 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00118 ^ 1 * a07865 ^ 1)
theorem ha07866 : a07866.IsHomogeneous 84 := by
  unfold a07866
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00118.pow 1)).mul (ha07865.pow 1)))

@[irreducible]
def a07867 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a07866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00004 ^ 2 * a00123 ^ 1)
theorem ha07867 : a07867.IsHomogeneous 103 := by
  unfold a07867
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha07866.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00123.pow 1)))

@[irreducible]
def a07868 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6)
theorem ha07868 : a07868.IsHomogeneous 6 := by
  unfold a07868
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6)))

@[irreducible]
def a07869 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00017 ^ 1 * a07868 ^ 1)
theorem ha07869 : a07869.IsHomogeneous 19 := by
  unfold a07869
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00017.pow 1)).mul (ha07868.pow 1)))

@[irreducible]
def a07870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a07868 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a07869 ^ 1)
theorem ha07870 : a07870.IsHomogeneous 30 := by
  unfold a07870
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha07868.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha07869.pow 1)))

@[irreducible]
def a07871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00032 ^ 1 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha07871 : a07871.IsHomogeneous 19 := by
  unfold a07871
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00032.pow 1)).mul (ha07868.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a07872 : Poly := (C ((-216 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a07868 ^ 1 * a07870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a07871 ^ 2)
theorem ha07872 : a07872.IsHomogeneous 43 := by
  unfold a07872
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-216 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha07868.pow 1)).mul (ha07870.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha07871.pow 2)))

@[irreducible]
def a07873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07868 ^ 1)
theorem ha07873 : a07873.IsHomogeneous 6 := by
  unfold a07873
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a07874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 2) + (C ((216 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a00025 ^ 2 * a07868 ^ 1 * a07873 ^ 2)
theorem ha07874 : a07874.IsHomogeneous 86 := by
  unfold a07874
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 2)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha00025.pow 2)).mul (ha07868.pow 1)).mul (ha07873.pow 2)))

@[irreducible]
def a07875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07874 ^ 1) + (C ((432 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a00025 ^ 2 * a07868 ^ 1 * a07873 ^ 2)
theorem ha07875 : a07875.IsHomogeneous 86 := by
  unfold a07875
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07874.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha00025.pow 2)).mul (ha07868.pow 1)).mul (ha07873.pow 2)))

@[irreducible]
def a07876 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (3 : ℂ)) * a07868 ^ 1)
theorem ha07876 : a07876.IsHomogeneous 6 := by
  unfold a07876
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a07877 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a07876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6)
theorem ha07877 : a07877.IsHomogeneous 6 := by
  unfold a07877
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha07876.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6)))

@[irreducible]
def a07878 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1)
theorem ha07878 : a07878.IsHomogeneous 6 := by
  unfold a07878
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a07879 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a07878 ^ 1)
theorem ha07879 : a07879.IsHomogeneous 19 := by
  unfold a07879
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha07868.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha07878.pow 1)))

@[irreducible]
def a07880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a07878 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07879 ^ 1)
theorem ha07880 : a07880.IsHomogeneous 19 := by
  unfold a07880
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha07878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07879.pow 1)))

@[irreducible]
def a07881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha07881 : a07881.IsHomogeneous 6 := by
  unfold a07881
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a07882 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a07881 ^ 1)
theorem ha07882 : a07882.IsHomogeneous 19 := by
  unfold a07882
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha07868.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha07881.pow 1)))

@[irreducible]
def a07883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07882 ^ 1)
theorem ha07883 : a07883.IsHomogeneous 19 := by
  unfold a07883
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07882.pow 1)))

@[irreducible]
def a07884 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a07878 ^ 1)
theorem ha07884 : a07884.IsHomogeneous 18 := by
  unfold a07884
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha07878.pow 1)))

@[irreducible]
def a07885 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a07884 ^ 1)
theorem ha07885 : a07885.IsHomogeneous 18 := by
  unfold a07885
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07884.pow 1)))

@[irreducible]
def a07886 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a07881 ^ 1)
theorem ha07886 : a07886.IsHomogeneous 18 := by
  unfold a07886
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha07881.pow 1)))

@[irreducible]
def a07887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07886 ^ 1)
theorem ha07887 : a07887.IsHomogeneous 18 := by
  unfold a07887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07886.pow 1)))

@[irreducible]
def a07888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07868 ^ 1 * a07887 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07883 ^ 1)
theorem ha07888 : a07888.IsHomogeneous 30 := by
  unfold a07888
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07868.pow 1)).mul (ha07887.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07883.pow 1)))

@[irreducible]
def a07889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha07889 : a07889.IsHomogeneous 6 := by
  unfold a07889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a07890 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1)
theorem ha07890 : a07890.IsHomogeneous 6 := by
  unfold a07890
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)))

@[irreducible]
def a07891 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07879 ^ 1 * a07890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07868 ^ 1 * a07884 ^ 1 * a07889 ^ 1)
theorem ha07891 : a07891.IsHomogeneous 36 := by
  unfold a07891
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07879.pow 1)).mul (ha07890.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07868.pow 1)).mul (ha07884.pow 1)).mul (ha07889.pow 1)))

@[irreducible]
def a07892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a07888 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07891 ^ 1)
theorem ha07892 : a07892.IsHomogeneous 36 := by
  unfold a07892
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha07888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07891.pow 1)))

@[irreducible]
def a07893 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1)
theorem ha07893 : a07893.IsHomogeneous 13 := by
  unfold a07893
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a07894 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07893 ^ 1)
theorem ha07894 : a07894.IsHomogeneous 13 := by
  unfold a07894
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07893.pow 1)))

@[irreducible]
def a07895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha07895 : a07895.IsHomogeneous 6 := by
  unfold a07895
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a07896 : Poly := (C ((-1 : ℂ) / (3888 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a07868 ^ 1)
theorem ha07896 : a07896.IsHomogeneous 18 := by
  unfold a07896
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3888 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha07868.pow 1)))

@[irreducible]
def a07897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a07895 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07896 ^ 1)
theorem ha07897 : a07897.IsHomogeneous 18 := by
  unfold a07897
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha07895.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07896.pow 1)))

@[irreducible]
def a07898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07897 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07894 ^ 1)
theorem ha07898 : a07898.IsHomogeneous 24 := by
  unfold a07898
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07897.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07894.pow 1)))

@[irreducible]
def a07899 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a07895 ^ 1)
theorem ha07899 : a07899.IsHomogeneous 19 := by
  unfold a07899
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha07868.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha07895.pow 1)))

@[irreducible]
def a07900 : Poly := (C ((-1 : ℂ) / (1944 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a07895 ^ 1)
theorem ha07900 : a07900.IsHomogeneous 18 := by
  unfold a07900
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha07895.pow 1)))

@[irreducible]
def a07901 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1)
theorem ha07901 : a07901.IsHomogeneous 6 := by
  unfold a07901
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a07902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07900 ^ 1 * a07901 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07899 ^ 1)
theorem ha07902 : a07902.IsHomogeneous 30 := by
  unfold a07902
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07900.pow 1)).mul (ha07901.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07899.pow 1)))

@[irreducible]
def a07903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a07898 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07902 ^ 1)
theorem ha07903 : a07903.IsHomogeneous 30 := by
  unfold a07903
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha07898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07902.pow 1)))

@[irreducible]
def a07904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07892 ^ 1)
theorem ha07904 : a07904.IsHomogeneous 36 := by
  unfold a07904
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07903.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07892.pow 1)))

@[irreducible]
def a07905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 2) + (C ((1 : ℂ) / (2 : ℂ)) * a07874 ^ 1)
theorem ha07905 : a07905.IsHomogeneous 86 := by
  unfold a07905
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07874.pow 1)))

@[irreducible]
def a07906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07883 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a07887 ^ 1)
theorem ha07906 : a07906.IsHomogeneous 25 := by
  unfold a07906
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07883.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07887.pow 1)))

@[irreducible]
def a07907 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a07884 ^ 1 * a07890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07879 ^ 1 * a07889 ^ 1)
theorem ha07907 : a07907.IsHomogeneous 31 := by
  unfold a07907
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07884.pow 1)).mul (ha07890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07879.pow 1)).mul (ha07889.pow 1)))

@[irreducible]
def a07908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a07906 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07907 ^ 1)
theorem ha07908 : a07908.IsHomogeneous 31 := by
  unfold a07908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha07906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07907.pow 1)))

@[irreducible]
def a07909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07868 ^ 1 * a07894 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a07897 ^ 1)
theorem ha07909 : a07909.IsHomogeneous 25 := by
  unfold a07909
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07868.pow 1)).mul (ha07894.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07897.pow 1)))

@[irreducible]
def a07910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07899 ^ 1 * a07901 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a07868 ^ 1 * a07900 ^ 1)
theorem ha07910 : a07910.IsHomogeneous 31 := by
  unfold a07910
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07899.pow 1)).mul (ha07901.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07868.pow 1)).mul (ha07900.pow 1)))

@[irreducible]
def a07911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a07909 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07910 ^ 1)
theorem ha07911 : a07911.IsHomogeneous 31 := by
  unfold a07911
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha07909.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07910.pow 1)))

@[irreducible]
def a07912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07908 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07911 ^ 1)
theorem ha07912 : a07912.IsHomogeneous 31 := by
  unfold a07912
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07911.pow 1)))

@[irreducible]
def a07913 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 3 * a00025 ^ 1 * a07868 ^ 1 * a07873 ^ 1 * a07905 ^ 1 * a07912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a07875 ^ 1 * a07904 ^ 1)
theorem ha07913 : a07913.IsHomogeneous 165 := by
  unfold a07913
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).mul (ha07868.pow 1)).mul (ha07873.pow 1)).mul (ha07905.pow 1)).mul (ha07912.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha07875.pow 1)).mul (ha07904.pow 1)))

@[irreducible]
def a07914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07870 ^ 2) + (C ((1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a07873 ^ 2)
theorem ha07914 : a07914.IsHomogeneous 66 := by
  unfold a07914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07870.pow 2)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha07873.pow 2)))

@[irreducible]
def a07915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a07868 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3)
theorem ha07915 : a07915.IsHomogeneous 18 := by
  unfold a07915
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha07868.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)))

@[irreducible]
def a07916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a07868 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07915 ^ 1)
theorem ha07916 : a07916.IsHomogeneous 18 := by
  unfold a07916
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha07868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07915.pow 1)))

@[irreducible]
def a07917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07915 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3)
theorem ha07917 : a07917.IsHomogeneous 18 := by
  unfold a07917
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07915.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)))

@[irreducible]
def a07918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00014 ^ 3 * a07868 ^ 1 * a07870 ^ 1 * a07873 ^ 1 * a07917 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07914 ^ 1 * a07916 ^ 1)
theorem ha07918 : a07918.IsHomogeneous 84 := by
  unfold a07918
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha07868.pow 1)).mul (ha07870.pow 1)).mul (ha07873.pow 1)).mul (ha07917.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07914.pow 1)).mul (ha07916.pow 1)))

@[irreducible]
def a07919 : Poly := (C ((-54 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a07868 ^ 1 * a07870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a07871 ^ 2)
theorem ha07919 : a07919.IsHomogeneous 43 := by
  unfold a07919
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-54 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha07868.pow 1)).mul (ha07870.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha07871.pow 2)))

@[irreducible]
def a07920 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 2 * a07868 ^ 1 * a07871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07919 ^ 1)
theorem ha07920 : a07920.IsHomogeneous 49 := by
  unfold a07920
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 2)).mul (ha07868.pow 1)).mul (ha07871.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07919.pow 1)))

@[irreducible]
def a07921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00017 ^ 1 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha07921 : a07921.IsHomogeneous 19 := by
  unfold a07921
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00017.pow 1)).mul (ha07868.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a07922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a07868 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a07921 ^ 1)
theorem ha07922 : a07922.IsHomogeneous 30 := by
  unfold a07922
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha07868.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha07921.pow 1)))

@[irreducible]
def a07923 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00009 ^ 1 * a00014 ^ 6 * a00025 ^ 1 * a07868 ^ 1 * a07873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07920 ^ 1 * a07922 ^ 1)
theorem ha07923 : a07923.IsHomogeneous 79 := by
  unfold a07923
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 6)).mul (ha00025.pow 1)).mul (ha07868.pow 1)).mul (ha07873.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07920.pow 1)).mul (ha07922.pow 1)))

@[irreducible]
def a07924 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 1 * a07871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07870 ^ 1)
theorem ha07924 : a07924.IsHomogeneous 36 := by
  unfold a07924
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha07871.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07870.pow 1)))

@[irreducible]
def a07925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07870 ^ 1 * a07924 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00009 ^ 1 * a00014 ^ 6 * a07873 ^ 2)
theorem ha07925 : a07925.IsHomogeneous 72 := by
  unfold a07925
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07870.pow 1)).mul (ha07924.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 6)).mul (ha07873.pow 2)))

@[irreducible]
def a07926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07923 ^ 1) + (C ((54 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a07925 ^ 1)
theorem ha07926 : a07926.IsHomogeneous 79 := by
  unfold a07926
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07923.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha07925.pow 1)))

@[irreducible]
def a07927 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00025 ^ 2 * a07868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07871 ^ 1)
theorem ha07927 : a07927.IsHomogeneous 25 := by
  unfold a07927
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00025.pow 2)).mul (ha07868.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07871.pow 1)))

@[irreducible]
def a07928 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a07868 ^ 1 * a07870 ^ 1 * a07927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07926 ^ 1)
theorem ha07928 : a07928.IsHomogeneous 79 := by
  unfold a07928
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha07868.pow 1)).mul (ha07870.pow 1)).mul (ha07927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07926.pow 1)))

@[irreducible]
def a07929 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 3 * a00002 ^ 1 * a00003 ^ 2 * a07920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00025 ^ 1 * a07873 ^ 1 * a07895 ^ 1)
theorem ha07929 : a07929.IsHomogeneous 55 := by
  unfold a07929
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha07920.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).mul (ha07873.pow 1)).mul (ha07895.pow 1)))

@[irreducible]
def a07930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a07870 ^ 1 * a07927 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a07929 ^ 1)
theorem ha07930 : a07930.IsHomogeneous 57 := by
  unfold a07930
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha07870.pow 1)).mul (ha07927.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha07929.pow 1)))

@[irreducible]
def a07931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a07868 ^ 1 * a07930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07928 ^ 1)
theorem ha07931 : a07931.IsHomogeneous 85 := by
  unfold a07931
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha07868.pow 1)).mul (ha07930.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07928.pow 1)))

@[irreducible]
def a07932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07914 ^ 1 * a07917 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 3 * a07870 ^ 1 * a07873 ^ 1 * a07916 ^ 1)
theorem ha07932 : a07932.IsHomogeneous 90 := by
  unfold a07932
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07914.pow 1)).mul (ha07917.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 3)).mul (ha07870.pow 1)).mul (ha07873.pow 1)).mul (ha07916.pow 1)))

@[irreducible]
def a07933 : Poly := (C ((-27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a07873 ^ 1 * a07922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07920 ^ 1)
theorem ha07933 : a07933.IsHomogeneous 49 := by
  unfold a07933
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha07873.pow 1)).mul (ha07922.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07920.pow 1)))

@[irreducible]
def a07934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07924 ^ 1)
theorem ha07934 : a07934.IsHomogeneous 36 := by
  unfold a07934
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07870.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07924.pow 1)))

@[irreducible]
def a07935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07933 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a07873 ^ 1 * a07934 ^ 1)
theorem ha07935 : a07935.IsHomogeneous 49 := by
  unfold a07935
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07933.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha07873.pow 1)).mul (ha07934.pow 1)))

end CycleQ2Concrete
