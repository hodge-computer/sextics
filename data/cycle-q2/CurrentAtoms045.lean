import Proposal.CurrentAtoms044

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a13312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13287 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13311 ^ 1)
theorem ha13312 : a13312.IsHomogeneous 252 := by
  unfold a13312
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13287.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13311.pow 1)))

@[irreducible]
def a13313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a13312 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00309 ^ 1 * a07463 ^ 1)
theorem ha13313 : a13313.IsHomogeneous 300 := by
  unfold a13313
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha13312.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00309.pow 1)).mul (ha07463.pow 1)))

@[irreducible]
def a13314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a13313 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a13218 ^ 1)
theorem ha13314 : a13314.IsHomogeneous 330 := by
  unfold a13314
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha13313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha13218.pow 1)))

@[irreducible]
def a13315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13314 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a13219 ^ 1)
theorem ha13315 : a13315.IsHomogeneous 330 := by
  unfold a13315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13314.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha13219.pow 1)))

@[irreducible]
def a13316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13315 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a13220 ^ 1)
theorem ha13316 : a13316.IsHomogeneous 330 := by
  unfold a13316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13315.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha13220.pow 1)))

@[irreducible]
def a13317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13316 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a13221 ^ 1)
theorem ha13317 : a13317.IsHomogeneous 330 := by
  unfold a13317
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha13221.pow 1)))

@[irreducible]
def a13318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13317 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a13277 ^ 1)
theorem ha13318 : a13318.IsHomogeneous 330 := by
  unfold a13318
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha13277.pow 1)))

@[irreducible]
def a13319 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a13318 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a07468 ^ 1)
theorem ha13319 : a13319.IsHomogeneous 756 := by
  unfold a13319
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha13318.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha07468.pow 1)))

@[irreducible]
def a13320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13203 ^ 1)
theorem ha13320 : a13320.IsHomogeneous 1089 := by
  unfold a13320
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13203.pow 1)))

@[irreducible]
def a13321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13320 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13204 ^ 1)
theorem ha13321 : a13321.IsHomogeneous 1422 := by
  unfold a13321
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13320.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13204.pow 1)))

@[irreducible]
def a13322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13205 ^ 1)
theorem ha13322 : a13322.IsHomogeneous 1755 := by
  unfold a13322
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13205.pow 1)))

@[irreducible]
def a13323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13322 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13206 ^ 1)
theorem ha13323 : a13323.IsHomogeneous 2088 := by
  unfold a13323
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13322.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13206.pow 1)))

@[irreducible]
def a13324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13323 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13211 ^ 1)
theorem ha13324 : a13324.IsHomogeneous 2421 := by
  unfold a13324
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13211.pow 1)))

@[irreducible]
def a13325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13196 ^ 1) + (C ((32 : ℂ) / (3645 : ℂ)) * a00042 ^ 6 * a13324 ^ 1)
theorem ha13325 : a13325.IsHomogeneous 2565 := by
  unfold a13325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13196.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3645 : ℂ))).mul (ha00042.pow 6)).mul (ha13324.pow 1)))

@[irreducible]
def a13326 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a07474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13325 ^ 1)
theorem ha13326 : a13326.IsHomogeneous 2625 := by
  unfold a13326
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha07474.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13325.pow 1)))

@[irreducible]
def a13327 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10700 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13326 ^ 1)
theorem ha13327 : a13327.IsHomogeneous 2685 := by
  unfold a13327
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10700.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13326.pow 1)))

@[irreducible]
def a13328 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10701 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13327 ^ 1)
theorem ha13328 : a13328.IsHomogeneous 2745 := by
  unfold a13328
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10701.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13327.pow 1)))

@[irreducible]
def a13329 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13328 ^ 1)
theorem ha13329 : a13329.IsHomogeneous 2805 := by
  unfold a13329
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13328.pow 1)))

@[irreducible]
def a13330 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13329 ^ 1)
theorem ha13330 : a13330.IsHomogeneous 2865 := by
  unfold a13330
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13329.pow 1)))

@[irreducible]
def a13331 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a01986 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02041 ^ 1 * a04045 ^ 1)
theorem ha13331 : a13331.IsHomogeneous 492 := by
  unfold a13331
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha01986.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02041.pow 1)).mul (ha04045.pow 1)))

@[irreducible]
def a13332 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a02041 ^ 1 * a04045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a07491 ^ 1)
theorem ha13332 : a13332.IsHomogeneous 552 := by
  unfold a13332
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).mul (ha04045.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha07491.pow 1)))

@[irreducible]
def a13333 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13331 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13332 ^ 1)
theorem ha13333 : a13333.IsHomogeneous 552 := by
  unfold a13333
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13331.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13332.pow 1)))

@[irreducible]
def a13334 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a07663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01986 ^ 1 * a04148 ^ 1)
theorem ha13334 : a13334.IsHomogeneous 432 := by
  unfold a13334
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha07663.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01986.pow 1)).mul (ha04148.pow 1)))

@[irreducible]
def a13335 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13331 ^ 1)
theorem ha13335 : a13335.IsHomogeneous 492 := by
  unfold a13335
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13331.pow 1)))

@[irreducible]
def a13336 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13333 ^ 1)
theorem ha13336 : a13336.IsHomogeneous 552 := by
  unfold a13336
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13333.pow 1)))

@[irreducible]
def a13337 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02041 ^ 1 * a04043 ^ 1)
theorem ha13337 : a13337.IsHomogeneous 390 := by
  unfold a13337
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02041.pow 1)).mul (ha04043.pow 1)))

@[irreducible]
def a13338 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a02041 ^ 1 * a04043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a07488 ^ 1)
theorem ha13338 : a13338.IsHomogeneous 450 := by
  unfold a13338
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).mul (ha04043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha07488.pow 1)))

@[irreducible]
def a13339 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13338 ^ 1)
theorem ha13339 : a13339.IsHomogeneous 450 := by
  unfold a13339
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13338.pow 1)))

@[irreducible]
def a13340 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a07663 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04148 ^ 1)
theorem ha13340 : a13340.IsHomogeneous 330 := by
  unfold a13340
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha07663.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04148.pow 1)))

@[irreducible]
def a13341 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a13340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13337 ^ 1)
theorem ha13341 : a13341.IsHomogeneous 390 := by
  unfold a13341
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha13340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13337.pow 1)))

@[irreducible]
def a13342 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13339 ^ 1)
theorem ha13342 : a13342.IsHomogeneous 450 := by
  unfold a13342
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13341.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13339.pow 1)))

@[irreducible]
def a13343 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a02041 ^ 1)
theorem ha13343 : a13343.IsHomogeneous 288 := by
  unfold a13343
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a13344 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a07486 ^ 1)
theorem ha13344 : a13344.IsHomogeneous 348 := by
  unfold a13344
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha07486.pow 1)))

@[irreducible]
def a13345 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a13343 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13344 ^ 1)
theorem ha13345 : a13345.IsHomogeneous 348 := by
  unfold a13345
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha13343.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13344.pow 1)))

@[irreducible]
def a13346 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00134 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00880 ^ 1)
theorem ha13346 : a13346.IsHomogeneous 246 := by
  unfold a13346
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a13347 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 2)
theorem ha13347 : a13347.IsHomogeneous 204 := by
  unfold a13347
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 2)))

@[irreducible]
def a13348 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13347 ^ 1)
theorem ha13348 : a13348.IsHomogeneous 204 := by
  unfold a13348
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13347.pow 1)))

@[irreducible]
def a13349 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a13348 ^ 1)
theorem ha13349 : a13349.IsHomogeneous 306 := by
  unfold a13349
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13346.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha13348.pow 1)))

@[irreducible]
def a13350 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a07486 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a13349 ^ 1)
theorem ha13350 : a13350.IsHomogeneous 408 := by
  unfold a13350
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha07486.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha13349.pow 1)))

@[irreducible]
def a13351 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13344 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13350 ^ 1)
theorem ha13351 : a13351.IsHomogeneous 408 := by
  unfold a13351
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13344.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13350.pow 1)))

@[irreducible]
def a13352 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13345 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13351 ^ 1)
theorem ha13352 : a13352.IsHomogeneous 408 := by
  unfold a13352
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13351.pow 1)))

@[irreducible]
def a13353 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a07488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a13352 ^ 1)
theorem ha13353 : a13353.IsHomogeneous 510 := by
  unfold a13353
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha07488.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha13352.pow 1)))

@[irreducible]
def a13354 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13338 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13353 ^ 1)
theorem ha13354 : a13354.IsHomogeneous 510 := by
  unfold a13354
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13338.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13353.pow 1)))

@[irreducible]
def a13355 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13354 ^ 1)
theorem ha13355 : a13355.IsHomogeneous 510 := by
  unfold a13355
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13339.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13354.pow 1)))

@[irreducible]
def a13356 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13355 ^ 1)
theorem ha13356 : a13356.IsHomogeneous 510 := by
  unfold a13356
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13342.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13355.pow 1)))

@[irreducible]
def a13357 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a07491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a13356 ^ 1)
theorem ha13357 : a13357.IsHomogeneous 612 := by
  unfold a13357
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha07491.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha13356.pow 1)))

@[irreducible]
def a13358 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13357 ^ 1)
theorem ha13358 : a13358.IsHomogeneous 612 := by
  unfold a13358
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13357.pow 1)))

@[irreducible]
def a13359 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13358 ^ 1)
theorem ha13359 : a13359.IsHomogeneous 612 := by
  unfold a13359
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13358.pow 1)))

@[irreducible]
def a13360 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a13336 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13359 ^ 1)
theorem ha13360 : a13360.IsHomogeneous 612 := by
  unfold a13360
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha13336.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13359.pow 1)))

@[irreducible]
def a13361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02032 ^ 1 * a02038 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00878 ^ 1 * a04131 ^ 1)
theorem ha13361 : a13361.IsHomogeneous 183 := by
  unfold a13361
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02032.pow 1)).mul (ha02038.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00878.pow 1)).mul (ha04131.pow 1)))

@[irreducible]
def a13362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00876 ^ 1 * a04144 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a02032 ^ 1 * a02038 ^ 1)
theorem ha13362 : a13362.IsHomogeneous 225 := by
  unfold a13362
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00876.pow 1)).mul (ha04144.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02032.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a13363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13362 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13361 ^ 1)
theorem ha13363 : a13363.IsHomogeneous 225 := by
  unfold a13363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13362.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13361.pow 1)))

@[irreducible]
def a13364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a04131 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a07634 ^ 1)
theorem ha13364 : a13364.IsHomogeneous 138 := by
  unfold a13364
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha04131.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha07634.pow 1)))

@[irreducible]
def a13365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13361 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13364 ^ 1)
theorem ha13365 : a13365.IsHomogeneous 183 := by
  unfold a13365
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13361.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13364.pow 1)))

@[irreducible]
def a13366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13363 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13365 ^ 1)
theorem ha13366 : a13366.IsHomogeneous 225 := by
  unfold a13366
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13365.pow 1)))

@[irreducible]
def a13367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00326 ^ 1 * a07658 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00876 ^ 1 * a04144 ^ 1)
theorem ha13367 : a13367.IsHomogeneous 267 := by
  unfold a13367
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00326.pow 1)).mul (ha07658.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00876.pow 1)).mul (ha04144.pow 1)))

@[irreducible]
def a13368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13367 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13362 ^ 1)
theorem ha13368 : a13368.IsHomogeneous 267 := by
  unfold a13368
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13367.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13362.pow 1)))

@[irreducible]
def a13369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13368 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13363 ^ 1)
theorem ha13369 : a13369.IsHomogeneous 267 := by
  unfold a13369
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13363.pow 1)))

@[irreducible]
def a13370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13369 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13366 ^ 1)
theorem ha13370 : a13370.IsHomogeneous 267 := by
  unfold a13370
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13369.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13366.pow 1)))

@[irreducible]
def a13371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a01896 ^ 1)
theorem ha13371 : a13371.IsHomogeneous 48 := by
  unfold a13371
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a13372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a00809 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha13372 : a13372.IsHomogeneous 51 := by
  unfold a13372
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00298 ^ 1 * a02008 ^ 1)
theorem ha13373 : a13373.IsHomogeneous 51 := by
  unfold a13373
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00298.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13372 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13371 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13373 ^ 1)
theorem ha13374 : a13374.IsHomogeneous 51 := by
  unfold a13374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13371.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13373.pow 1)))

@[irreducible]
def a13375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00317 ^ 1 * a00809 ^ 1)
theorem ha13375 : a13375.IsHomogeneous 48 := by
  unfold a13375
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00129 ^ 1 * a03890 ^ 1)
theorem ha13376 : a13376.IsHomogeneous 48 := by
  unfold a13376
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00129.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13376 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a13375 ^ 1)
theorem ha13377 : a13377.IsHomogeneous 48 := by
  unfold a13377
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13376.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha13375.pow 1)))

@[irreducible]
def a13378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha13378 : a13378.IsHomogeneous 51 := by
  unfold a13378
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13372 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13378 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a13375 ^ 1)
theorem ha13379 : a13379.IsHomogeneous 51 := by
  unfold a13379
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13372.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13378.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha13375.pow 1)))

@[irreducible]
def a13380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13374 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13379 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13377 ^ 1)
theorem ha13380 : a13380.IsHomogeneous 51 := by
  unfold a13380
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13374.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13379.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13377.pow 1)))

@[irreducible]
def a13381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha13381 : a13381.IsHomogeneous 51 := by
  unfold a13381
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha13382 : a13382.IsHomogeneous 51 := by
  unfold a13382
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a13383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13372 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a13382 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a13381 ^ 1)
theorem ha13383 : a13383.IsHomogeneous 51 := by
  unfold a13383
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13372.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha13382.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha13381.pow 1)))

@[irreducible]
def a13384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00126 ^ 1 * a04086 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a02008 ^ 1)
theorem ha13384 : a13384.IsHomogeneous 48 := by
  unfold a13384
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00126.pow 1)).mul (ha04086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13373 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a13384 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a13381 ^ 1)
theorem ha13385 : a13385.IsHomogeneous 51 := by
  unfold a13385
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha13384.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha13381.pow 1)))

@[irreducible]
def a13386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13374 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13383 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13385 ^ 1)
theorem ha13386 : a13386.IsHomogeneous 51 := by
  unfold a13386
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13374.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13383.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13385.pow 1)))

@[irreducible]
def a13387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha13387 : a13387.IsHomogeneous 51 := by
  unfold a13387
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a13388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13378 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a13387 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a13382 ^ 1)
theorem ha13388 : a13388.IsHomogeneous 51 := by
  unfold a13388
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13378.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha13387.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha13382.pow 1)))

@[irreducible]
def a13389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13383 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13388 ^ 1)
theorem ha13389 : a13389.IsHomogeneous 51 := by
  unfold a13389
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13383.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13388.pow 1)))

@[irreducible]
def a13390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13380 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13389 ^ 1)
theorem ha13390 : a13390.IsHomogeneous 51 := by
  unfold a13390
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13386.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13389.pow 1)))

@[irreducible]
def a13391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a03890 ^ 1)
theorem ha13391 : a13391.IsHomogeneous 51 := by
  unfold a13391
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha13392 : a13392.IsHomogeneous 51 := by
  unfold a13392
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a13393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13391 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13392 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a13375 ^ 1)
theorem ha13393 : a13393.IsHomogeneous 51 := by
  unfold a13393
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13391.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13392.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha13375.pow 1)))

@[irreducible]
def a13394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03890 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a07248 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03890 ^ 1)
theorem ha13394 : a13394.IsHomogeneous 51 := by
  unfold a13394
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha07248.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13391 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13376 ^ 1) + (C ((14 : ℂ) / (27 : ℂ)) * a13394 ^ 1)
theorem ha13395 : a13395.IsHomogeneous 51 := by
  unfold a13395
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13391.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13376.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (27 : ℂ))).mul (ha13394.pow 1)))

@[irreducible]
def a13396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13395 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13377 ^ 1)
theorem ha13396 : a13396.IsHomogeneous 51 := by
  unfold a13396
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13393.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13395.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13377.pow 1)))

@[irreducible]
def a13397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00298 ^ 1)
theorem ha13397 : a13397.IsHomogeneous 54 := by
  unfold a13397
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a13398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13378 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13392 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a13397 ^ 1)
theorem ha13398 : a13398.IsHomogeneous 54 := by
  unfold a13398
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13378.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13392.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha13397.pow 1)))

@[irreducible]
def a13399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13379 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13393 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13398 ^ 1)
theorem ha13399 : a13399.IsHomogeneous 54 := by
  unfold a13399
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13379.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13393.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13398.pow 1)))

@[irreducible]
def a13400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13380 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13399 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13396 ^ 1)
theorem ha13400 : a13400.IsHomogeneous 54 := by
  unfold a13400
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13399.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13396.pow 1)))

@[irreducible]
def a13401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a13397 ^ 1)
theorem ha13401 : a13401.IsHomogeneous 54 := by
  unfold a13401
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha13397.pow 1)))

@[irreducible]
def a13402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13398 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a13401 ^ 1)
theorem ha13402 : a13402.IsHomogeneous 54 := by
  unfold a13402
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13398.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha13401.pow 1)))

@[irreducible]
def a13403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13399 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13402 ^ 1)
theorem ha13403 : a13403.IsHomogeneous 54 := by
  unfold a13403
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13399.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13402.pow 1)))

@[irreducible]
def a13404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13403 ^ 1)
theorem ha13404 : a13404.IsHomogeneous 54 := by
  unfold a13404
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13400.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13403.pow 1)))

@[irreducible]
def a13405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01896 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02008 ^ 1)
theorem ha13405 : a13405.IsHomogeneous 48 := by
  unfold a13405
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01896.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01896 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00865 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00317 ^ 1 * a03890 ^ 1)
theorem ha13406 : a13406.IsHomogeneous 48 := by
  unfold a13406
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00865.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00317.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13405 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13406 ^ 1)
theorem ha13407 : a13407.IsHomogeneous 48 := by
  unfold a13407
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13405.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13406.pow 1)))

@[irreducible]
def a13408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a04086 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a02008 ^ 1)
theorem ha13408 : a13408.IsHomogeneous 48 := by
  unfold a13408
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13373 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13405 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a13408 ^ 1)
theorem ha13409 : a13409.IsHomogeneous 51 := by
  unfold a13409
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13405.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha13408.pow 1)))

@[irreducible]
def a13410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13374 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13407 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13409 ^ 1)
theorem ha13410 : a13410.IsHomogeneous 51 := by
  unfold a13410
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13374.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13407.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13409.pow 1)))

@[irreducible]
def a13411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a03890 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a07248 ^ 1)
theorem ha13411 : a13411.IsHomogeneous 48 := by
  unfold a13411
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha03890.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a13412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13376 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13406 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a13411 ^ 1)
theorem ha13412 : a13412.IsHomogeneous 48 := by
  unfold a13412
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13406.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha13411.pow 1)))

@[irreducible]
def a13413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13377 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13407 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13412 ^ 1)
theorem ha13413 : a13413.IsHomogeneous 48 := by
  unfold a13413
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13407.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13412.pow 1)))

@[irreducible]
def a13414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13380 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13410 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13413 ^ 1)
theorem ha13414 : a13414.IsHomogeneous 51 := by
  unfold a13414
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13410.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13413.pow 1)))

@[irreducible]
def a13415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07558 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a04086 ^ 1)
theorem ha13415 : a13415.IsHomogeneous 48 := by
  unfold a13415
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07558.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a13416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13384 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13415 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a13408 ^ 1)
theorem ha13416 : a13416.IsHomogeneous 48 := by
  unfold a13416
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13415.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha13408.pow 1)))

@[irreducible]
def a13417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13409 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a13416 ^ 1)
theorem ha13417 : a13417.IsHomogeneous 51 := by
  unfold a13417
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13409.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha13416.pow 1)))

@[irreducible]
def a13418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13410 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a13417 ^ 1)
theorem ha13418 : a13418.IsHomogeneous 51 := by
  unfold a13418
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13410.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha13417.pow 1)))

@[irreducible]
def a13419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13418 ^ 1)
theorem ha13419 : a13419.IsHomogeneous 51 := by
  unfold a13419
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13414.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13418.pow 1)))

@[irreducible]
def a13420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a07248 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a12998 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a07248 ^ 1)
theorem ha13420 : a13420.IsHomogeneous 48 := by
  unfold a13420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha12998.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a13421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13394 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a13420 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13411 ^ 1)
theorem ha13421 : a13421.IsHomogeneous 51 := by
  unfold a13421
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13394.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha13420.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13411.pow 1)))

@[irreducible]
def a13422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13395 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13412 ^ 1) + (C ((14 : ℂ) / (27 : ℂ)) * a13421 ^ 1)
theorem ha13422 : a13422.IsHomogeneous 51 := by
  unfold a13422
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13395.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13412.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (27 : ℂ))).mul (ha13421.pow 1)))

@[irreducible]
def a13423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13396 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13422 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13413 ^ 1)
theorem ha13423 : a13423.IsHomogeneous 51 := by
  unfold a13423
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13396.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13422.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13413.pow 1)))

@[irreducible]
def a13424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13400 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13423 ^ 1)
theorem ha13424 : a13424.IsHomogeneous 54 := by
  unfold a13424
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13414.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13400.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13423.pow 1)))

@[irreducible]
def a13425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13424 ^ 1)
theorem ha13425 : a13425.IsHomogeneous 54 := by
  unfold a13425
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13404.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13424.pow 1)))

@[irreducible]
def a13426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01617 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00865 ^ 1 * a03432 ^ 1)
theorem ha13426 : a13426.IsHomogeneous 54 := by
  unfold a13426
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01617.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00865.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a13427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00655 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a01617 ^ 1 * a02008 ^ 1)
theorem ha13427 : a13427.IsHomogeneous 51 := by
  unfold a13427
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00655.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha01617.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13427 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13426 ^ 1)
theorem ha13428 : a13428.IsHomogeneous 54 := by
  unfold a13428
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13427.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13426.pow 1)))

@[irreducible]
def a13429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a06529 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00865 ^ 1 * a03432 ^ 1)
theorem ha13429 : a13429.IsHomogeneous 54 := by
  unfold a13429
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha06529.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00865.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a13430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13426 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13429 ^ 1)
theorem ha13430 : a13430.IsHomogeneous 54 := by
  unfold a13430
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13429.pow 1)))

@[irreducible]
def a13431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13428 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13430 ^ 1)
theorem ha13431 : a13431.IsHomogeneous 54 := by
  unfold a13431
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13428.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13430.pow 1)))

@[irreducible]
def a13432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00218 ^ 1 * a07558 ^ 1)
theorem ha13432 : a13432.IsHomogeneous 54 := by
  unfold a13432
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00218.pow 1)).mul (ha07558.pow 1)))

@[irreducible]
def a13433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13427 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13432 ^ 1)
theorem ha13433 : a13433.IsHomogeneous 54 := by
  unfold a13433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13427.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13432.pow 1)))

@[irreducible]
def a13434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13428 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13433 ^ 1)
theorem ha13434 : a13434.IsHomogeneous 54 := by
  unfold a13434
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13428.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13433.pow 1)))

@[irreducible]
def a13435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13434 ^ 1)
theorem ha13435 : a13435.IsHomogeneous 54 := by
  unfold a13435
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13434.pow 1)))

@[irreducible]
def a13436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a11923 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00317 ^ 1 * a06529 ^ 1)
theorem ha13436 : a13436.IsHomogeneous 51 := by
  unfold a13436
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha11923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00317.pow 1)).mul (ha06529.pow 1)))

@[irreducible]
def a13437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13436 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13429 ^ 1)
theorem ha13437 : a13437.IsHomogeneous 54 := by
  unfold a13437
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13429.pow 1)))

@[irreducible]
def a13438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13430 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a13437 ^ 1)
theorem ha13438 : a13438.IsHomogeneous 54 := by
  unfold a13438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13430.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha13437.pow 1)))

@[irreducible]
def a13439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13431 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13438 ^ 1)
theorem ha13439 : a13439.IsHomogeneous 54 := by
  unfold a13439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13438.pow 1)))

@[irreducible]
def a13440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13439 ^ 1)
theorem ha13440 : a13440.IsHomogeneous 54 := by
  unfold a13440
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13439.pow 1)))

@[irreducible]
def a13441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1)
theorem ha13441 : a13441.IsHomogeneous 6 := by
  unfold a13441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)))

@[irreducible]
def a13442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01325 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13441 ^ 1)
theorem ha13442 : a13442.IsHomogeneous 6 := by
  unfold a13442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13441.pow 1)))

@[irreducible]
def a13443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02931 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05749 ^ 1)
theorem ha13443 : a13443.IsHomogeneous 6 := by
  unfold a13443
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02931.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05749.pow 1)))

@[irreducible]
def a13444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13443 ^ 1)
theorem ha13444 : a13444.IsHomogeneous 6 := by
  unfold a13444
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13441.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13443.pow 1)))

@[irreducible]
def a13445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13442 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13444 ^ 1)
theorem ha13445 : a13445.IsHomogeneous 6 := by
  unfold a13445
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13444.pow 1)))

@[irreducible]
def a13446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01326 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a13442 ^ 1)
theorem ha13446 : a13446.IsHomogeneous 6 := by
  unfold a13446
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha13442.pow 1)))

@[irreducible]
def a13447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13445 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a13446 ^ 1)
theorem ha13447 : a13447.IsHomogeneous 6 := by
  unfold a13447
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha13446.pow 1)))

@[irreducible]
def a13448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05749 ^ 1) + (C ((252 : ℂ) / (5 : ℂ)) * a10773 ^ 1)
theorem ha13448 : a13448.IsHomogeneous 6 := by
  unfold a13448
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05749.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((252 : ℂ) / (5 : ℂ))).mul (ha10773.pow 1)))

@[irreducible]
def a13449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13443 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13448 ^ 1)
theorem ha13449 : a13449.IsHomogeneous 6 := by
  unfold a13449
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13443.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13448.pow 1)))

@[irreducible]
def a13450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13444 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13449 ^ 1)
theorem ha13450 : a13450.IsHomogeneous 6 := by
  unfold a13450
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13449.pow 1)))

@[irreducible]
def a13451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13445 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a13450 ^ 1)
theorem ha13451 : a13451.IsHomogeneous 6 := by
  unfold a13451
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha13450.pow 1)))

@[irreducible]
def a13452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13447 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13451 ^ 1)
theorem ha13452 : a13452.IsHomogeneous 6 := by
  unfold a13452
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13447.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13451.pow 1)))

@[irreducible]
def a13453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13446 ^ 1)
theorem ha13453 : a13453.IsHomogeneous 6 := by
  unfold a13453
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13446.pow 1)))

@[irreducible]
def a13454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13447 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a13453 ^ 1)
theorem ha13454 : a13454.IsHomogeneous 6 := by
  unfold a13454
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13447.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha13453.pow 1)))

@[irreducible]
def a13455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13454 ^ 1)
theorem ha13455 : a13455.IsHomogeneous 6 := by
  unfold a13455
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13452.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13454.pow 1)))

@[irreducible]
def a13456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a13455 ^ 1) + (C ((7 : ℂ) / (270 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha13456 : a13456.IsHomogeneous 15 := by
  unfold a13456
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha13455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (270 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a13457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00064 ^ 1 * a13456 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a07558 ^ 1)
theorem ha13457 : a13457.IsHomogeneous 54 := by
  unfold a13457
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)).mul (ha13456.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha07558.pow 1)))

@[irreducible]
def a13458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13432 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a13457 ^ 1)
theorem ha13458 : a13458.IsHomogeneous 54 := by
  unfold a13458
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13432.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha13457.pow 1)))

@[irreducible]
def a13459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13458 ^ 1)
theorem ha13459 : a13459.IsHomogeneous 54 := by
  unfold a13459
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13458.pow 1)))

@[irreducible]
def a13460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13434 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13459 ^ 1)
theorem ha13460 : a13460.IsHomogeneous 54 := by
  unfold a13460
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13434.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13459.pow 1)))

@[irreducible]
def a13461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13460 ^ 1)
theorem ha13461 : a13461.IsHomogeneous 54 := by
  unfold a13461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13460.pow 1)))

@[irreducible]
def a13462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13461 ^ 1)
theorem ha13462 : a13462.IsHomogeneous 54 := by
  unfold a13462
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13461.pow 1)))

@[irreducible]
def a13463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00621 ^ 1 * a00865 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00317 ^ 1 * a01555 ^ 1)
theorem ha13463 : a13463.IsHomogeneous 48 := by
  unfold a13463
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00621.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00317.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a13464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a00621 ^ 1)
theorem ha13464 : a13464.IsHomogeneous 48 := by
  unfold a13464
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a13465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00621 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a02008 ^ 1)
theorem ha13465 : a13465.IsHomogeneous 48 := by
  unfold a13465
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00621.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13463 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13464 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13465 ^ 1)
theorem ha13466 : a13466.IsHomogeneous 48 := by
  unfold a13466
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13464.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13465.pow 1)))

@[irreducible]
def a13467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00129 ^ 1 * a01555 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a00621 ^ 1)
theorem ha13467 : a13467.IsHomogeneous 48 := by
  unfold a13467
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00129.pow 1)).mul (ha01555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a13468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03330 ^ 1)
theorem ha13468 : a13468.IsHomogeneous 48 := by
  unfold a13468
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a13469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13463 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13467 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a13468 ^ 1)
theorem ha13469 : a13469.IsHomogeneous 48 := by
  unfold a13469
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13467.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha13468.pow 1)))

@[irreducible]
def a13470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00129 ^ 1 * a00621 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00201 ^ 1 * a00317 ^ 1)
theorem ha13470 : a13470.IsHomogeneous 48 := by
  unfold a13470
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00129.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a13471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13467 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a13470 ^ 1)
theorem ha13471 : a13471.IsHomogeneous 48 := by
  unfold a13471
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13467.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha13470.pow 1)))

@[irreducible]
def a13472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13466 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13469 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13471 ^ 1)
theorem ha13472 : a13472.IsHomogeneous 48 := by
  unfold a13472
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13466.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13469.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13471.pow 1)))

@[irreducible]
def a13473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00621 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00130 ^ 1 * a00865 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00621 ^ 1 * a00865 ^ 1)
theorem ha13473 : a13473.IsHomogeneous 54 := by
  unfold a13473
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00621.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00317 ^ 1 * a03330 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00865 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a01555 ^ 1)
theorem ha13474 : a13474.IsHomogeneous 54 := by
  unfold a13474
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a13475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13463 ^ 1) + (C ((4 : ℂ) / (35 : ℂ)) * a13474 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a13473 ^ 1)
theorem ha13475 : a13475.IsHomogeneous 54 := by
  unfold a13475
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (35 : ℂ))).mul (ha13474.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha13473.pow 1)))

@[irreducible]
def a13476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00621 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a02008 ^ 1)
theorem ha13476 : a13476.IsHomogeneous 51 := by
  unfold a13476
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00621.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13476 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13473 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a13465 ^ 1)
theorem ha13477 : a13477.IsHomogeneous 54 := by
  unfold a13477
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13476.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13473.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha13465.pow 1)))

@[irreducible]
def a13478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13466 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13475 ^ 1) + (C ((24 : ℂ) / (175 : ℂ)) * a13477 ^ 1)
theorem ha13478 : a13478.IsHomogeneous 54 := by
  unfold a13478
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13466.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13475.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (175 : ℂ))).mul (ha13477.pow 1)))

@[irreducible]
def a13479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a03330 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a03330 ^ 1)
theorem ha13479 : a13479.IsHomogeneous 51 := by
  unfold a13479
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a13480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13479 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a13474 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a13468 ^ 1)
theorem ha13480 : a13480.IsHomogeneous 54 := by
  unfold a13480
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha13474.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha13468.pow 1)))

@[irreducible]
def a13481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13475 ^ 1) + (C ((8 : ℂ) / (175 : ℂ)) * a13480 ^ 1)
theorem ha13481 : a13481.IsHomogeneous 54 := by
  unfold a13481
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13475.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (175 : ℂ))).mul (ha13480.pow 1)))

@[irreducible]
def a13482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13472 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13481 ^ 1)
theorem ha13482 : a13482.IsHomogeneous 54 := by
  unfold a13482
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13478.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13481.pow 1)))

@[irreducible]
def a13483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a02008 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00865 ^ 1)
theorem ha13483 : a13483.IsHomogeneous 51 := by
  unfold a13483
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00054 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00317 ^ 1)
theorem ha13484 : a13484.IsHomogeneous 51 := by
  unfold a13484
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00054.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a13485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13483 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13484 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13464 ^ 1)
theorem ha13485 : a13485.IsHomogeneous 51 := by
  unfold a13485
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13484.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13464.pow 1)))

@[irreducible]
def a13486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a04086 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a02008 ^ 1)
theorem ha13486 : a13486.IsHomogeneous 48 := by
  unfold a13486
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13483 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a13486 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13465 ^ 1)
theorem ha13487 : a13487.IsHomogeneous 51 := by
  unfold a13487
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13483.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha13486.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13465.pow 1)))

@[irreducible]
def a13488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13487 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a13466 ^ 1)
theorem ha13488 : a13488.IsHomogeneous 51 := by
  unfold a13488
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13487.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha13466.pow 1)))

@[irreducible]
def a13489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha13489 : a13489.IsHomogeneous 51 := by
  unfold a13489
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a13490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13484 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13489 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a13470 ^ 1)
theorem ha13490 : a13490.IsHomogeneous 51 := by
  unfold a13490
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13489.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha13470.pow 1)))

@[irreducible]
def a13491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13485 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13490 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13471 ^ 1)
theorem ha13491 : a13491.IsHomogeneous 51 := by
  unfold a13491
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13490.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13471.pow 1)))

@[irreducible]
def a13492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13491 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a13472 ^ 1)
theorem ha13492 : a13492.IsHomogeneous 51 := by
  unfold a13492
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13491.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha13472.pow 1)))

@[irreducible]
def a13493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a04086 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a07558 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a04086 ^ 1)
theorem ha13493 : a13493.IsHomogeneous 54 := by
  unfold a13493
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha07558.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a13494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13476 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13493 ^ 1) + (C ((35 : ℂ) / (36 : ℂ)) * a00003 ^ 6 * a13486 ^ 1)
theorem ha13494 : a13494.IsHomogeneous 54 := by
  unfold a13494
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13476.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13493.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (36 : ℂ))).mul (ha00003.pow 6)).mul (ha13486.pow 1)))

@[irreducible]
def a13495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13487 ^ 1) + (C ((27 : ℂ) / (35 : ℂ)) * a13477 ^ 1) + (C ((27 : ℂ) / (35 : ℂ)) * a13494 ^ 1)
theorem ha13495 : a13495.IsHomogeneous 54 := by
  unfold a13495
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13487.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (35 : ℂ))).mul (ha13477.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (35 : ℂ))).mul (ha13494.pow 1)))

@[irreducible]
def a13496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13495 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a13478 ^ 1)
theorem ha13496 : a13496.IsHomogeneous 54 := by
  unfold a13496
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13495.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha13478.pow 1)))

@[irreducible]
def a13497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13496 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a13482 ^ 1)
theorem ha13497 : a13497.IsHomogeneous 54 := by
  unfold a13497
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13496.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha13482.pow 1)))

@[irreducible]
def a13498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a03330 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01555 ^ 1)
theorem ha13498 : a13498.IsHomogeneous 51 := by
  unfold a13498
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a13499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01555 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00621 ^ 1)
theorem ha13499 : a13499.IsHomogeneous 51 := by
  unfold a13499
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a13500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13498 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a13499 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13467 ^ 1)
theorem ha13500 : a13500.IsHomogeneous 51 := by
  unfold a13500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha13499.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13467.pow 1)))

@[irreducible]
def a13501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03330 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a06376 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03330 ^ 1)
theorem ha13501 : a13501.IsHomogeneous 48 := by
  unfold a13501
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03330.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha06376.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a13502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13498 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a13501 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13468 ^ 1)
theorem ha13502 : a13502.IsHomogeneous 51 := by
  unfold a13502
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13498.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha13501.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13468.pow 1)))

@[irreducible]
def a13503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13500 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13502 ^ 1) + (C ((135 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a13469 ^ 1)
theorem ha13503 : a13503.IsHomogeneous 51 := by
  unfold a13503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13500.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13502.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha13469.pow 1)))

@[irreducible]
def a13504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha13504 : a13504.IsHomogeneous 51 := by
  unfold a13504
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a13505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13499 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13504 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a13470 ^ 1)
theorem ha13505 : a13505.IsHomogeneous 51 := by
  unfold a13505
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13504.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha13470.pow 1)))

@[irreducible]
def a13506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13500 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a13505 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13471 ^ 1)
theorem ha13506 : a13506.IsHomogeneous 51 := by
  unfold a13506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13500.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha13505.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13471.pow 1)))

@[irreducible]
def a13507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13503 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13506 ^ 1) + (C ((135 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a13472 ^ 1)
theorem ha13507 : a13507.IsHomogeneous 51 := by
  unfold a13507
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13506.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha13472.pow 1)))

@[irreducible]
def a13508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a11703 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a06376 ^ 1)
theorem ha13508 : a13508.IsHomogeneous 54 := by
  unfold a13508
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha11703.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha06376.pow 1)))

@[irreducible]
def a13509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13508 ^ 1) + (C ((35 : ℂ) / (36 : ℂ)) * a00003 ^ 6 * a13501 ^ 1)
theorem ha13509 : a13509.IsHomogeneous 54 := by
  unfold a13509
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13508.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (36 : ℂ))).mul (ha00003.pow 6)).mul (ha13501.pow 1)))

@[irreducible]
def a13510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13502 ^ 1) + (C ((27 : ℂ) / (35 : ℂ)) * a13480 ^ 1) + (C ((27 : ℂ) / (35 : ℂ)) * a13509 ^ 1)
theorem ha13510 : a13510.IsHomogeneous 54 := by
  unfold a13510
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13502.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (35 : ℂ))).mul (ha13480.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (35 : ℂ))).mul (ha13509.pow 1)))

@[irreducible]
def a13511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13503 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13510 ^ 1) + (C ((135 : ℂ) / (8 : ℂ)) * a13481 ^ 1)
theorem ha13511 : a13511.IsHomogeneous 54 := by
  unfold a13511
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13510.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (8 : ℂ))).mul (ha13481.pow 1)))

@[irreducible]
def a13512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13511 ^ 1) + (C ((135 : ℂ) / (8 : ℂ)) * a13482 ^ 1)
theorem ha13512 : a13512.IsHomogeneous 54 := by
  unfold a13512
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13511.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (8 : ℂ))).mul (ha13482.pow 1)))

@[irreducible]
def a13513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00054 ^ 1)
theorem ha13513 : a13513.IsHomogeneous 54 := by
  unfold a13513
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)))

@[irreducible]
def a13514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13513 ^ 1)
theorem ha13514 : a13514.IsHomogeneous 54 := by
  unfold a13514
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13489.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13504.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13513.pow 1)))

@[irreducible]
def a13515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13490 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13505 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a13514 ^ 1)
theorem ha13515 : a13515.IsHomogeneous 54 := by
  unfold a13515
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13490.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13505.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha13514.pow 1)))

@[irreducible]
def a13516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13491 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13506 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a13515 ^ 1)
theorem ha13516 : a13516.IsHomogeneous 54 := by
  unfold a13516
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13491.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13506.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha13515.pow 1)))

@[irreducible]
def a13517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13516 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a13507 ^ 1)
theorem ha13517 : a13517.IsHomogeneous 54 := by
  unfold a13517
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13516.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha13507.pow 1)))

@[irreducible]
def a13518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13497 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13517 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13512 ^ 1)
theorem ha13518 : a13518.IsHomogeneous 54 := by
  unfold a13518
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13497.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13517.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13512.pow 1)))

@[irreducible]
def a13519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00324 ^ 1 * a00632 ^ 1 * a00865 ^ 1)
theorem ha13519 : a13519.IsHomogeneous 39 := by
  unfold a13519
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00324.pow 1)).mul (ha00632.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a00632 ^ 1)
theorem ha13520 : a13520.IsHomogeneous 33 := by
  unfold a13520
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a13521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00207 ^ 1 * a00324 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00324 ^ 1 * a00632 ^ 1 * a00865 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00865 ^ 1)
theorem ha13521 : a13521.IsHomogeneous 39 := by
  unfold a13521
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00324.pow 1)).mul (ha00632.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13520 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a13521 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a13519 ^ 1)
theorem ha13522 : a13522.IsHomogeneous 39 := by
  unfold a13522
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha13521.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha13519.pow 1)))

@[irreducible]
def a13523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01575 ^ 1)
theorem ha13523 : a13523.IsHomogeneous 33 := by
  unfold a13523
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00632.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a13524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01575 ^ 1)
theorem ha13524 : a13524.IsHomogeneous 33 := by
  unfold a13524
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a13525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13523 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13519 ^ 1)
theorem ha13525 : a13525.IsHomogeneous 39 := by
  unfold a13525
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13523.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13524.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13519.pow 1)))

@[irreducible]
def a13526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00207 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a00632 ^ 1)
theorem ha13526 : a13526.IsHomogeneous 33 := by
  unfold a13526
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a13527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13526 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a13523 ^ 1)
theorem ha13527 : a13527.IsHomogeneous 33 := by
  unfold a13527
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13526.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha13523.pow 1)))

@[irreducible]
def a13528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13527 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13522 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a13525 ^ 1)
theorem ha13528 : a13528.IsHomogeneous 39 := by
  unfold a13528
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13527.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13522.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha13525.pow 1)))

@[irreducible]
def a13529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00133 ^ 1 * a00632 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a00632 ^ 1 * a00865 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00865 ^ 1 * a01575 ^ 1)
theorem ha13529 : a13529.IsHomogeneous 39 := by
  unfold a13529
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha00632.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a13530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a03363 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00865 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha13530 : a13530.IsHomogeneous 33 := by
  unfold a13530
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00865.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a13531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13530 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a13529 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a13519 ^ 1)
theorem ha13531 : a13531.IsHomogeneous 39 := by
  unfold a13531
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13530.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha13529.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha13519.pow 1)))

@[irreducible]
def a13532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a04086 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a02008 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a02008 ^ 1)
theorem ha13532 : a13532.IsHomogeneous 36 := by
  unfold a13532
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13532 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a13529 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a13521 ^ 1)
theorem ha13533 : a13533.IsHomogeneous 39 := by
  unfold a13533
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13532.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha13529.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha13521.pow 1)))

@[irreducible]
def a13534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13522 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a13531 ^ 1) + (C ((1 : ℂ) / (105 : ℂ)) * a13533 ^ 1)
theorem ha13534 : a13534.IsHomogeneous 39 := by
  unfold a13534
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha13531.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (105 : ℂ))).mul (ha13533.pow 1)))

@[irreducible]
def a13535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a03363 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a03363 ^ 1)
theorem ha13535 : a13535.IsHomogeneous 33 := by
  unfold a13535
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a13536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13524 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a13535 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a13530 ^ 1)
theorem ha13536 : a13536.IsHomogeneous 33 := by
  unfold a13536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha13535.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha13530.pow 1)))

@[irreducible]
def a13537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13525 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a13531 ^ 1)
theorem ha13537 : a13537.IsHomogeneous 39 := by
  unfold a13537
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13536.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13525.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha13531.pow 1)))

@[irreducible]
def a13538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13534 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a13537 ^ 1)
theorem ha13538 : a13538.IsHomogeneous 39 := by
  unfold a13538
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13534.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha13537.pow 1)))

@[irreducible]
def a13539 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a02008 ^ 1)
theorem ha13539 : a13539.IsHomogeneous 33 := by
  unfold a13539
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13540 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00865 ^ 1)
theorem ha13540 : a13540.IsHomogeneous 33 := by
  unfold a13540
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a13541 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a13539 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a13540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13520 ^ 1)
theorem ha13541 : a13541.IsHomogeneous 33 := by
  unfold a13541
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha13539.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha13540.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13520.pow 1)))

@[irreducible]
def a13542 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a04086 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a02008 ^ 1)
theorem ha13542 : a13542.IsHomogeneous 36 := by
  unfold a13542
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha04086.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13543 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a13521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13542 ^ 1) + (C ((20 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13539 ^ 1)
theorem ha13543 : a13543.IsHomogeneous 39 := by
  unfold a13543
  exact ((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha13521.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13542.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13539.pow 1)))

@[irreducible]
def a13544 : Poly := (C ((-1 : ℂ) / (120 : ℂ)) * a13543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13522 ^ 1)
theorem ha13544 : a13544.IsHomogeneous 39 := by
  unfold a13544
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (120 : ℂ))).mul (ha13543.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13541.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13522.pow 1)))

@[irreducible]
def a13545 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00058 ^ 1 * a00317 ^ 1)
theorem ha13545 : a13545.IsHomogeneous 33 := by
  unfold a13545
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a13546 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a13540 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a13545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13526 ^ 1)
theorem ha13546 : a13546.IsHomogeneous 33 := by
  unfold a13546
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha13540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha13545.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13526.pow 1)))

@[irreducible]
def a13547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13527 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13541 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a13546 ^ 1)
theorem ha13547 : a13547.IsHomogeneous 33 := by
  unfold a13547
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13527.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13541.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha13546.pow 1)))

@[irreducible]
def a13548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13544 ^ 1)
theorem ha13548 : a13548.IsHomogeneous 39 := by
  unfold a13548
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13547.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13528.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13544.pow 1)))

@[irreducible]
def a13549 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a07558 ^ 1) + (C ((7 : ℂ) / (10 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a04086 ^ 1)
theorem ha13549 : a13549.IsHomogeneous 36 := by
  unfold a13549
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha07558.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (10 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a13550 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a13542 ^ 1) + (C ((-5 : ℂ) / (4 : ℂ)) * a13549 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13532 ^ 1)
theorem ha13550 : a13550.IsHomogeneous 36 := by
  unfold a13550
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha13542.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha13549.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13532.pow 1)))

@[irreducible]
def a13551 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a13543 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13533 ^ 1)
theorem ha13551 : a13551.IsHomogeneous 39 := by
  unfold a13551
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha13543.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13550.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13533.pow 1)))

@[irreducible]
def a13552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13544 ^ 1) + (C ((1 : ℂ) / (105 : ℂ)) * a13551 ^ 1)
theorem ha13552 : a13552.IsHomogeneous 39 := by
  unfold a13552
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13544.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (105 : ℂ))).mul (ha13551.pow 1)))

@[irreducible]
def a13553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13538 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13552 ^ 1)
theorem ha13553 : a13553.IsHomogeneous 39 := by
  unfold a13553
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13548.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13552.pow 1)))

@[irreducible]
def a13554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01575 ^ 1)
theorem ha13554 : a13554.IsHomogeneous 30 := by
  unfold a13554
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01575.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a13555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00632 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01575 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00632 ^ 1)
theorem ha13555 : a13555.IsHomogeneous 36 := by
  unfold a13555
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a13556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13555 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13554 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13523 ^ 1)
theorem ha13556 : a13556.IsHomogeneous 36 := by
  unfold a13556
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13554.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13523.pow 1)))

@[irreducible]
def a13557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a06426 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a03363 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00324 ^ 1 * a03363 ^ 1)
theorem ha13557 : a13557.IsHomogeneous 36 := by
  unfold a13557
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha06426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha03363.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a13558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13557 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a13554 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13524 ^ 1)
theorem ha13558 : a13558.IsHomogeneous 36 := by
  unfold a13558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13557.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha13554.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13524.pow 1)))

@[irreducible]
def a13559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13558 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a13525 ^ 1)
theorem ha13559 : a13559.IsHomogeneous 39 := by
  unfold a13559
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13556.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13558.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha13525.pow 1)))

@[irreducible]
def a13560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00632 ^ 1)
theorem ha13560 : a13560.IsHomogeneous 36 := by
  unfold a13560
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a13561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13555 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a13560 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a13526 ^ 1)
theorem ha13561 : a13561.IsHomogeneous 36 := by
  unfold a13561
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha13560.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha13526.pow 1)))

@[irreducible]
def a13562 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13556 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13561 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a00003 ^ 3 * a13527 ^ 1)
theorem ha13562 : a13562.IsHomogeneous 36 := by
  unfold a13562
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13556.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13561.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha00003.pow 3)).mul (ha13527.pow 1)))

@[irreducible]
def a13563 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13559 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a13528 ^ 1)
theorem ha13563 : a13563.IsHomogeneous 39 := by
  unfold a13563
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13559.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha13528.pow 1)))

@[irreducible]
def a13564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a11778 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a06426 ^ 1)
theorem ha13564 : a13564.IsHomogeneous 36 := by
  unfold a13564
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha11778.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha06426.pow 1)))

@[irreducible]
def a13565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13557 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a13564 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a13535 ^ 1)
theorem ha13565 : a13565.IsHomogeneous 36 := by
  unfold a13565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha13564.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha13535.pow 1)))

@[irreducible]
def a13566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13565 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13536 ^ 1)
theorem ha13566 : a13566.IsHomogeneous 36 := by
  unfold a13566
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13565.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13536.pow 1)))

@[irreducible]
def a13567 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13559 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a13537 ^ 1)
theorem ha13567 : a13567.IsHomogeneous 39 := by
  unfold a13567
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13566.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13559.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha13537.pow 1)))

end CycleQ2Concrete
