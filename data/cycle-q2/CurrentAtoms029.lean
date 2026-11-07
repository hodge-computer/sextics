import Proposal.CurrentAtoms028

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a09216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a04588 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00841 ^ 1 * a02242 ^ 1)
theorem ha09216 : a09216.IsHomogeneous 82 := by
  unfold a09216
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha04588.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00841.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a09217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a04588 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a00126 ^ 1 * a08965 ^ 1)
theorem ha09217 : a09217.IsHomogeneous 52 := by
  unfold a09217
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha04588.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha00126.pow 1)).mul (ha08965.pow 1)))

@[irreducible]
def a09218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a09217 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09216 ^ 1)
theorem ha09218 : a09218.IsHomogeneous 82 := by
  unfold a09218
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha09217.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09216.pow 1)))

@[irreducible]
def a09219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a02242 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00953 ^ 1 * a01962 ^ 1)
theorem ha09219 : a09219.IsHomogeneous 82 := by
  unfold a09219
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha02242.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00953.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a09220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09216 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a09219 ^ 1)
theorem ha09220 : a09220.IsHomogeneous 82 := by
  unfold a09220
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09216.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha09219.pow 1)))

@[irreducible]
def a09221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09218 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09220 ^ 1)
theorem ha09221 : a09221.IsHomogeneous 82 := by
  unfold a09221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09218.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09220.pow 1)))

@[irreducible]
def a09222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09215 ^ 1) + (C ((10 : ℂ) / (9 : ℂ)) * a09221 ^ 1)
theorem ha09222 : a09222.IsHomogeneous 82 := by
  unfold a09222
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (9 : ℂ))).mul (ha09221.pow 1)))

@[irreducible]
def a09223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09222 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a04738 ^ 1)
theorem ha09223 : a09223.IsHomogeneous 88 := by
  unfold a09223
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09222.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha04738.pow 1)))

@[irreducible]
def a09224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09223 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a09186 ^ 1)
theorem ha09224 : a09224.IsHomogeneous 94 := by
  unfold a09224
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha09186.pow 1)))

@[irreducible]
def a09225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00994 ^ 1 * a01841 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a02320 ^ 1)
theorem ha09225 : a09225.IsHomogeneous 96 := by
  unfold a09225
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00994.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha02320.pow 1)))

@[irreducible]
def a09226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09225 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a09186 ^ 1)
theorem ha09226 : a09226.IsHomogeneous 96 := by
  unfold a09226
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09225.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha09186.pow 1)))

@[irreducible]
def a09227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09224 ^ 1) + (C ((5 : ℂ) / (27 : ℂ)) * a00003 ^ 4 * a09226 ^ 1)
theorem ha09227 : a09227.IsHomogeneous 100 := by
  unfold a09227
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09224.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (27 : ℂ))).mul (ha00003.pow 4)).mul (ha09226.pow 1)))

@[irreducible]
def a09228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02574 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a01118 ^ 1 * a01275 ^ 1)
theorem ha09228 : a09228.IsHomogeneous 344 := by
  unfold a09228
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02574.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha01118.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a09229 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00404 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01118 ^ 1 * a01275 ^ 1)
theorem ha09229 : a09229.IsHomogeneous 308 := by
  unfold a09229
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01118.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a09230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09228 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a09229 ^ 1)
theorem ha09230 : a09230.IsHomogeneous 344 := by
  unfold a09230
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha09229.pow 1)))

@[irreducible]
def a09231 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00484 ^ 1 * a02574 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a05180 ^ 1)
theorem ha09231 : a09231.IsHomogeneous 344 := by
  unfold a09231
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00484.pow 1)).mul (ha02574.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha05180.pow 1)))

@[irreducible]
def a09232 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a09231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09228 ^ 1)
theorem ha09232 : a09232.IsHomogeneous 344 := by
  unfold a09232
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha09231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09228.pow 1)))

@[irreducible]
def a09233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09232 ^ 1)
theorem ha09233 : a09233.IsHomogeneous 344 := by
  unfold a09233
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09232.pow 1)))

@[irreducible]
def a09234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01092 ^ 1 * a01313 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a02520 ^ 1)
theorem ha09234 : a09234.IsHomogeneous 308 := by
  unfold a09234
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01092.pow 1)).mul (ha01313.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09235 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a02520 ^ 1)
theorem ha09235 : a09235.IsHomogeneous 272 := by
  unfold a09235
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09234 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a09235 ^ 1)
theorem ha09236 : a09236.IsHomogeneous 308 := by
  unfold a09236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09234.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha09235.pow 1)))

@[irreducible]
def a09237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a02904 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01092 ^ 1 * a01313 ^ 1)
theorem ha09237 : a09237.IsHomogeneous 344 := by
  unfold a09237
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha02904.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01092.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a09238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09237 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09234 ^ 1)
theorem ha09238 : a09238.IsHomogeneous 344 := by
  unfold a09238
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09237.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09234.pow 1)))

@[irreducible]
def a09239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09238 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09236 ^ 1)
theorem ha09239 : a09239.IsHomogeneous 344 := by
  unfold a09239
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09236.pow 1)))

@[irreducible]
def a09240 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a04689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a02295 ^ 1)
theorem ha09240 : a09240.IsHomogeneous 255 := by
  unfold a09240
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha04689.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a09241 : Poly := (C ((-12 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a04689 ^ 1)
theorem ha09241 : a09241.IsHomogeneous 189 := by
  unfold a09241
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha04689.pow 1)))

@[irreducible]
def a09242 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a09241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09240 ^ 1)
theorem ha09242 : a09242.IsHomogeneous 255 := by
  unfold a09242
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09240.pow 1)))

@[irreducible]
def a09243 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00982 ^ 1 * a01979 ^ 1)
theorem ha09243 : a09243.IsHomogeneous 291 := by
  unfold a09243
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00982.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a09244 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09243 ^ 1)
theorem ha09244 : a09244.IsHomogeneous 291 := by
  unfold a09244
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09240.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09243.pow 1)))

@[irreducible]
def a09245 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09244 ^ 1)
theorem ha09245 : a09245.IsHomogeneous 291 := by
  unfold a09245
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09244.pow 1)))

@[irreducible]
def a09246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a09245 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a09233 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a09239 ^ 1)
theorem ha09246 : a09246.IsHomogeneous 346 := by
  unfold a09246
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha09245.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha09233.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha09239.pow 1)))

@[irreducible]
def a09247 : Poly := (C ((-1 : ℂ) / (160 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 6 * a09227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09246 ^ 1)
theorem ha09247 : a09247.IsHomogeneous 346 := by
  unfold a09247
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (160 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 6)).mul (ha09227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09246.pow 1)))

@[irreducible]
def a09248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04752 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a09247 ^ 1)
theorem ha09248 : a09248.IsHomogeneous 346 := by
  unfold a09248
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04752.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha09247.pow 1)))

@[irreducible]
def a09249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09248 ^ 1)
theorem ha09249 : a09249.IsHomogeneous 346 := by
  unfold a09249
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09248.pow 1)))

@[irreducible]
def a09250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09249 ^ 1)
theorem ha09250 : a09250.IsHomogeneous 346 := by
  unfold a09250
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09249.pow 1)))

@[irreducible]
def a09251 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a09250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a04754 ^ 1)
theorem ha09251 : a09251.IsHomogeneous 772 := by
  unfold a09251
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha09250.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha04754.pow 1)))

@[irreducible]
def a09252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09180 ^ 1)
theorem ha09252 : a09252.IsHomogeneous 1105 := by
  unfold a09252
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09180.pow 1)))

@[irreducible]
def a09253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09182 ^ 1)
theorem ha09253 : a09253.IsHomogeneous 1438 := by
  unfold a09253
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09182.pow 1)))

@[irreducible]
def a09254 : Poly := (C ((-25 : ℂ) / (216 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 6 * a08869 ^ 1) + (C ((-2 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 2 * a08839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a09179 ^ 1) + (C ((1 : ℂ) / (77760 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 6 * a00100 ^ 7 * a02687 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 6 * a00100 ^ 2 * a08845 ^ 1) + (C ((10 : ℂ) / (9 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 3 * a00042 ^ 6 * a00100 ^ 1 * a08857 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a08851 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 1 * a08863 ^ 1) + (C ((64 : ℂ) / (27 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 6 * a09253 ^ 1)
theorem ha09254 : a09254.IsHomogeneous 1616 := by
  unfold a09254
  exact (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (216 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha08869.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha08839.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha09179.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (77760 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 6)).mul (ha00100.pow 7)).mul (ha02687.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 6)).mul (ha00100.pow 2)).mul (ha08845.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (9 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 6)).mul (ha00100.pow 1)).mul (ha08857.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha08851.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 1)).mul (ha08863.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (27 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha09253.pow 1)))

@[irreducible]
def a09255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a02376 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a04821 ^ 1)
theorem ha09255 : a09255.IsHomogeneous 1327 := by
  unfold a09255
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha02376.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha04821.pow 1)))

@[irreducible]
def a09256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02375 ^ 1)
theorem ha09256 : a09256.IsHomogeneous 322 := by
  unfold a09256
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04819.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02375.pow 1)))

@[irreducible]
def a09257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a02375 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01026 ^ 1 * a02038 ^ 1)
theorem ha09257 : a09257.IsHomogeneous 322 := by
  unfold a09257
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha02375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01026.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a09258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09257 ^ 1)
theorem ha09258 : a09258.IsHomogeneous 322 := by
  unfold a09258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09257.pow 1)))

@[irreducible]
def a09259 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00368 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00368 ^ 1)
theorem ha09259 : a09259.IsHomogeneous 12 := by
  unfold a09259
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a09260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02413 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01041 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01041 ^ 1)
theorem ha09260 : a09260.IsHomogeneous 18 := by
  unfold a09260
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01041.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01041.pow 1)))

@[irreducible]
def a09261 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00368 ^ 1) + (C ((-3 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1)
theorem ha09261 : a09261.IsHomogeneous 12 := by
  unfold a09261
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)))

@[irreducible]
def a09262 : Poly := (C ((-45 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a09259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09260 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09261 ^ 1)
theorem ha09262 : a09262.IsHomogeneous 18 := by
  unfold a09262
  exact (((((isHomogeneous_C (σ := Fin 6) ((-45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha09259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09260.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09261.pow 1)))

@[irreducible]
def a09263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a02413 ^ 1)
theorem ha09263 : a09263.IsHomogeneous 18 := by
  unfold a09263
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01041.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha02413.pow 1)))

@[irreducible]
def a09264 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00368 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01041 ^ 1)
theorem ha09264 : a09264.IsHomogeneous 18 := by
  unfold a09264
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00368.pow 1)).mul (ha00864.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a09265 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a09259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09263 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09264 ^ 1)
theorem ha09265 : a09265.IsHomogeneous 18 := by
  unfold a09265
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha09259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09263.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09264.pow 1)))

@[irreducible]
def a09266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02413 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a04894 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a02413 ^ 1)
theorem ha09266 : a09266.IsHomogeneous 24 := by
  unfold a09266
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha04894.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha02413.pow 1)))

@[irreducible]
def a09267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09266 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09263 ^ 1)
theorem ha09267 : a09267.IsHomogeneous 24 := by
  unfold a09267
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09266.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09263.pow 1)))

@[irreducible]
def a09268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09267 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09265 ^ 1)
theorem ha09268 : a09268.IsHomogeneous 24 := by
  unfold a09268
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09267.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09265.pow 1)))

@[irreducible]
def a09269 : Poly := (C ((-1 : ℂ) / (162 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a04169 ^ 1)
theorem ha09269 : a09269.IsHomogeneous 54 := by
  unfold a09269
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (162 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09268.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha04169.pow 1)))

@[irreducible]
def a09270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00455 ^ 1)
theorem ha09270 : a09270.IsHomogeneous 18 := by
  unfold a09270
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a09271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a01207 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00455 ^ 1)
theorem ha09271 : a09271.IsHomogeneous 24 := by
  unfold a09271
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha01207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a09272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00506 ^ 1)
theorem ha09272 : a09272.IsHomogeneous 24 := by
  unfold a09272
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a09273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09272 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09270 ^ 1)
theorem ha09273 : a09273.IsHomogeneous 24 := by
  unfold a09273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09271.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09272.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09270.pow 1)))

@[irreducible]
def a09274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1)
theorem ha09274 : a09274.IsHomogeneous 18 := by
  unfold a09274
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)))

@[irreducible]
def a09275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00455 ^ 1)
theorem ha09275 : a09275.IsHomogeneous 12 := by
  unfold a09275
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a09276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09270 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a09275 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a09274 ^ 1)
theorem ha09276 : a09276.IsHomogeneous 18 := by
  unfold a09276
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09270.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha09275.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha09274.pow 1)))

@[irreducible]
def a09277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01207 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01207 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a02710 ^ 1)
theorem ha09277 : a09277.IsHomogeneous 18 := by
  unfold a09277
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01207.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha02710.pow 1)))

@[irreducible]
def a09278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09271 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a09277 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a09274 ^ 1)
theorem ha09278 : a09278.IsHomogeneous 24 := by
  unfold a09278
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09271.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha09277.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha09274.pow 1)))

@[irreducible]
def a09279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09278 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09276 ^ 1)
theorem ha09279 : a09279.IsHomogeneous 24 := by
  unfold a09279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09278.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09276.pow 1)))

@[irreducible]
def a09280 : Poly := (C ((-81 : ℂ) / (10 : ℂ)) * a09279 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09268 ^ 1)
theorem ha09280 : a09280.IsHomogeneous 24 := by
  unfold a09280
  exact (((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (10 : ℂ))).mul (ha09279.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09268.pow 1)))

@[irreducible]
def a09281 : Poly := (C ((-1 : ℂ) / (162 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09269 ^ 1)
theorem ha09281 : a09281.IsHomogeneous 54 := by
  unfold a09281
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (162 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09269.pow 1)))

@[irreducible]
def a09282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a04169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09269 ^ 1)
theorem ha09282 : a09282.IsHomogeneous 54 := by
  unfold a09282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha04169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09269.pow 1)))

@[irreducible]
def a09283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09282 ^ 1)
theorem ha09283 : a09283.IsHomogeneous 54 := by
  unfold a09283
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09281.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09282.pow 1)))

@[irreducible]
def a09284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a04179 ^ 1) + (C ((1 : ℂ) / (80 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09279 ^ 1)
theorem ha09284 : a09284.IsHomogeneous 54 := by
  unfold a09284
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha04179.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (80 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09279.pow 1)))

@[irreducible]
def a09285 : Poly := (C ((-1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09284 ^ 1)
theorem ha09285 : a09285.IsHomogeneous 54 := by
  unfold a09285
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09284.pow 1)))

@[irreducible]
def a09286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09281 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a09285 ^ 1)
theorem ha09286 : a09286.IsHomogeneous 54 := by
  unfold a09286
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09281.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha09285.pow 1)))

@[irreducible]
def a09287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09286 ^ 1)
theorem ha09287 : a09287.IsHomogeneous 54 := by
  unfold a09287
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09286.pow 1)))

@[irreducible]
def a09288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02996 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a03256 ^ 1)
theorem ha09288 : a09288.IsHomogeneous 30 := by
  unfold a09288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02996.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha03256.pow 1)))

@[irreducible]
def a09289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03269 ^ 1) + (C ((2 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03256 ^ 1)
theorem ha09289 : a09289.IsHomogeneous 57 := by
  unfold a09289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03269.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03256.pow 1)))

@[irreducible]
def a09290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09289 ^ 1) + (C ((1 : ℂ) / (90 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a09288 ^ 1)
theorem ha09290 : a09290.IsHomogeneous 57 := by
  unfold a09290
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09289.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (90 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09288.pow 1)))

@[irreducible]
def a09291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03540 ^ 1) + (C ((1 : ℂ) / (288 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a02996 ^ 1)
theorem ha09291 : a09291.IsHomogeneous 54 := by
  unfold a09291
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03540.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02996.pow 1)))

@[irreducible]
def a09292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09291 ^ 1) + (C ((1 : ℂ) / (288 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a09288 ^ 1)
theorem ha09292 : a09292.IsHomogeneous 54 := by
  unfold a09292
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09291.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09288.pow 1)))

@[irreducible]
def a09293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09292 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a09290 ^ 1)
theorem ha09293 : a09293.IsHomogeneous 57 := by
  unfold a09293
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha09290.pow 1)))

@[irreducible]
def a09294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09289 ^ 1)
theorem ha09294 : a09294.IsHomogeneous 57 := by
  unfold a09294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09289.pow 1)))

@[irreducible]
def a09295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09290 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09294 ^ 1)
theorem ha09295 : a09295.IsHomogeneous 57 := by
  unfold a09295
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09294.pow 1)))

@[irreducible]
def a09296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09293 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a09295 ^ 1)
theorem ha09296 : a09296.IsHomogeneous 57 := by
  unfold a09296
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09293.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha09295.pow 1)))

@[irreducible]
def a09297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03285 ^ 1) + (C ((1 : ℂ) / (56 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a03061 ^ 1)
theorem ha09297 : a09297.IsHomogeneous 57 := by
  unfold a09297
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03285.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (56 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03061.pow 1)))

@[irreducible]
def a09298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09297 ^ 1) + (C ((1 : ℂ) / (56 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a03061 ^ 1)
theorem ha09298 : a09298.IsHomogeneous 57 := by
  unfold a09298
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09297.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (56 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03061.pow 1)))

@[irreducible]
def a09299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03041 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03061 ^ 1)
theorem ha09299 : a09299.IsHomogeneous 24 := by
  unfold a09299
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03061.pow 1)))

@[irreducible]
def a09300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09299 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03061 ^ 1)
theorem ha09300 : a09300.IsHomogeneous 24 := by
  unfold a09300
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09299.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03061.pow 1)))

@[irreducible]
def a09301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09297 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09299 ^ 1)
theorem ha09301 : a09301.IsHomogeneous 57 := by
  unfold a09301
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09297.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09299.pow 1)))

@[irreducible]
def a09302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09301 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09300 ^ 1)
theorem ha09302 : a09302.IsHomogeneous 57 := by
  unfold a09302
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09301.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09300.pow 1)))

@[irreducible]
def a09303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03307 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a03041 ^ 1)
theorem ha09303 : a09303.IsHomogeneous 57 := by
  unfold a09303
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03307.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03041.pow 1)))

@[irreducible]
def a09304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09303 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09299 ^ 1)
theorem ha09304 : a09304.IsHomogeneous 57 := by
  unfold a09304
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09303.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09299.pow 1)))

@[irreducible]
def a09305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09303 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a03041 ^ 1)
theorem ha09305 : a09305.IsHomogeneous 57 := by
  unfold a09305
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09303.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03041.pow 1)))

@[irreducible]
def a09306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09305 ^ 1) + (C ((3 : ℂ) / (70 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09300 ^ 1)
theorem ha09306 : a09306.IsHomogeneous 57 := by
  unfold a09306
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09304.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09305.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (70 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09300.pow 1)))

@[irreducible]
def a09307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09301 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09304 ^ 1)
theorem ha09307 : a09307.IsHomogeneous 57 := by
  unfold a09307
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09301.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09304.pow 1)))

@[irreducible]
def a09308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09306 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09307 ^ 1)
theorem ha09308 : a09308.IsHomogeneous 57 := by
  unfold a09308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09302.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09306.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09307.pow 1)))

@[irreducible]
def a09309 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00316 ^ 1 * a00510 ^ 1)
theorem ha09309 : a09309.IsHomogeneous 24 := by
  unfold a09309
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha01335.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00316.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a09310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00510 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00510 ^ 1)
theorem ha09310 : a09310.IsHomogeneous 24 := by
  unfold a09310
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a09311 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a02949 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a01335 ^ 1)
theorem ha09311 : a09311.IsHomogeneous 24 := by
  unfold a09311
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha02949.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a09312 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09309 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a09311 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09310 ^ 1)
theorem ha09312 : a09312.IsHomogeneous 30 := by
  unfold a09312
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09309.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha09311.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09310.pow 1)))

@[irreducible]
def a09313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00632 ^ 1)
theorem ha09313 : a09313.IsHomogeneous 24 := by
  unfold a09313
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a09314 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00156 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00316 ^ 1 * a00510 ^ 1)
theorem ha09314 : a09314.IsHomogeneous 30 := by
  unfold a09314
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00316.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a09315 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09313 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09314 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09309 ^ 1)
theorem ha09315 : a09315.IsHomogeneous 30 := by
  unfold a09315
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09313.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09314.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09309.pow 1)))

@[irreducible]
def a09316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00510 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a01575 ^ 1)
theorem ha09316 : a09316.IsHomogeneous 18 := by
  unfold a09316
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00632.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a09317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09310 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a09313 ^ 1) + (C ((126 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a09316 ^ 1)
theorem ha09317 : a09317.IsHomogeneous 24 := by
  unfold a09317
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09310.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha09313.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((126 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha09316.pow 1)))

@[irreducible]
def a09318 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a09315 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09312 ^ 1)
theorem ha09318 : a09318.IsHomogeneous 30 := by
  unfold a09318
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha09315.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09317.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09312.pow 1)))

@[irreducible]
def a09319 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09318 ^ 1)
theorem ha09319 : a09319.IsHomogeneous 30 := by
  unfold a09319
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09318.pow 1)))

@[irreducible]
def a09320 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09318 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a09319 ^ 1)
theorem ha09320 : a09320.IsHomogeneous 30 := by
  unfold a09320
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09318.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha09319.pow 1)))

@[irreducible]
def a09321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 1 * a09318 ^ 1)
theorem ha09321 : a09321.IsHomogeneous 48 := by
  unfold a09321
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03347.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09318.pow 1)))

@[irreducible]
def a09322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09321 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03347 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 1 * a09318 ^ 1)
theorem ha09322 : a09322.IsHomogeneous 48 := by
  unfold a09322
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09321.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03347.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09318.pow 1)))

@[irreducible]
def a09323 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 2 * a03100 ^ 1)
theorem ha09323 : a09323.IsHomogeneous 48 := by
  unfold a09323
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03347.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03100.pow 1)))

@[irreducible]
def a09324 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09323 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 2 * a03100 ^ 1)
theorem ha09324 : a09324.IsHomogeneous 48 := by
  unfold a09324
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09323.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha03100.pow 1)))

@[irreducible]
def a09325 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a09324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09322 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 1 * a09320 ^ 1)
theorem ha09325 : a09325.IsHomogeneous 48 := by
  unfold a09325
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha09324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09322.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha09320.pow 1)))

@[irreducible]
def a09326 : Poly := (C ((-7 : ℂ) / (6 : ℂ)) * a09308 ^ 1) + (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a09325 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09287 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a09296 ^ 1)
theorem ha09326 : a09326.IsHomogeneous 57 := by
  unfold a09326
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (6 : ℂ))).mul (ha09308.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha09325.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09287.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha09296.pow 1)))

@[irreducible]
def a09327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02655 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a01180 ^ 1)
theorem ha09327 : a09327.IsHomogeneous 284 := by
  unfold a09327
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02655.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a09328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00445 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01180 ^ 1)
theorem ha09328 : a09328.IsHomogeneous 246 := by
  unfold a09328
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00445.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a09329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09327 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a09328 ^ 1)
theorem ha09329 : a09329.IsHomogeneous 284 := by
  unfold a09329
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha09328.pow 1)))

@[irreducible]
def a09330 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a02655 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a05296 ^ 1)
theorem ha09330 : a09330.IsHomogeneous 320 := by
  unfold a09330
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha02655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha05296.pow 1)))

@[irreducible]
def a09331 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09330 ^ 1)
theorem ha09331 : a09331.IsHomogeneous 320 := by
  unfold a09331
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09330.pow 1)))

@[irreducible]
def a09332 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09331 ^ 1)
theorem ha09332 : a09332.IsHomogeneous 320 := by
  unfold a09332
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09331.pow 1)))

@[irreducible]
def a09333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00637 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a02104 ^ 1)
theorem ha09333 : a09333.IsHomogeneous 235 := by
  unfold a09333
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00637.pow 1)).mul (ha00931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a09334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00637 ^ 1 * a00931 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00362 ^ 1 * a01581 ^ 1)
theorem ha09334 : a09334.IsHomogeneous 197 := by
  unfold a09334
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00637.pow 1)).mul (ha00931.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a09334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09333 ^ 1)
theorem ha09335 : a09335.IsHomogeneous 235 := by
  unfold a09335
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha09334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09333.pow 1)))

@[irreducible]
def a09336 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a04232 ^ 1)
theorem ha09336 : a09336.IsHomogeneous 271 := by
  unfold a09336
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha02104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a09337 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a09333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09336 ^ 1)
theorem ha09337 : a09337.IsHomogeneous 271 := by
  unfold a09337
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha09333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09336.pow 1)))

@[irreducible]
def a09338 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a09335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09337 ^ 1)
theorem ha09338 : a09338.IsHomogeneous 271 := by
  unfold a09338
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha09335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09337.pow 1)))

@[irreducible]
def a09339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00880 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00327 ^ 1 * a00595 ^ 1)
theorem ha09339 : a09339.IsHomogeneous 187 := by
  unfold a09339
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00880.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a09340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00595 ^ 1) + (C ((8 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00134 ^ 1 * a01507 ^ 1)
theorem ha09340 : a09340.IsHomogeneous 150 := by
  unfold a09340
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00595.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha01507.pow 1)))

@[irreducible]
def a09341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09339 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a09340 ^ 1)
theorem ha09341 : a09341.IsHomogeneous 187 := by
  unfold a09341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09339.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha09340.pow 1)))

@[irreducible]
def a09342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a02041 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00880 ^ 1)
theorem ha09342 : a09342.IsHomogeneous 223 := by
  unfold a09342
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha02041.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a09343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09342 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09339 ^ 1)
theorem ha09343 : a09343.IsHomogeneous 223 := by
  unfold a09343
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09342.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09339.pow 1)))

@[irreducible]
def a09344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09343 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09341 ^ 1)
theorem ha09344 : a09344.IsHomogeneous 223 := by
  unfold a09344
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09343.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09341.pow 1)))

@[irreducible]
def a09345 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a09338 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a09344 ^ 1) + (C ((25 : ℂ) / (3456 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a09332 ^ 1)
theorem ha09345 : a09345.IsHomogeneous 322 := by
  unfold a09345
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha09338.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha09344.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (3456 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha09332.pow 1)))

@[irreducible]
def a09346 : Poly := (C ((-1 : ℂ) / (7776 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00003 ^ 3 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 6 * a00100 ^ 6 * a09326 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09345 ^ 1)
theorem ha09346 : a09346.IsHomogeneous 322 := by
  unfold a09346
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (7776 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00003.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 6)).mul (ha00100.pow 6)).mul (ha09326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09345.pow 1)))

@[irreducible]
def a09347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04819 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a09346 ^ 1)
theorem ha09347 : a09347.IsHomogeneous 322 := by
  unfold a09347
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04819.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha09346.pow 1)))

@[irreducible]
def a09348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09347 ^ 1)
theorem ha09348 : a09348.IsHomogeneous 322 := by
  unfold a09348
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09347.pow 1)))

@[irreducible]
def a09349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09348 ^ 1)
theorem ha09349 : a09349.IsHomogeneous 322 := by
  unfold a09349
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09348.pow 1)))

@[irreducible]
def a09350 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a09349 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a04821 ^ 1)
theorem ha09350 : a09350.IsHomogeneous 880 := by
  unfold a09350
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha09349.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha04821.pow 1)))

@[irreducible]
def a09351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09255 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a09350 ^ 1)
theorem ha09351 : a09351.IsHomogeneous 1327 := by
  unfold a09351
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09255.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha09350.pow 1)))

@[irreducible]
def a09352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01026 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a02376 ^ 1)
theorem ha09352 : a09352.IsHomogeneous 1744 := by
  unfold a09352
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01026.pow 1)).mul (ha02046.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a09353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09352 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09255 ^ 1)
theorem ha09353 : a09353.IsHomogeneous 1744 := by
  unfold a09353
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09352.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09255.pow 1)))

@[irreducible]
def a09354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09353 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09351 ^ 1)
theorem ha09354 : a09354.IsHomogeneous 1744 := by
  unfold a09354
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09353.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09351.pow 1)))

@[irreducible]
def a09355 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 3 * a09354 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 4 * a09254 ^ 1)
theorem ha09355 : a09355.IsHomogeneous 1856 := by
  unfold a09355
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha09354.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 4)).mul (ha09254.pow 1)))

@[irreducible]
def a09356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01180 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00935 ^ 1 * a02655 ^ 1)
theorem ha09356 : a09356.IsHomogeneous 1830 := by
  unfold a09356
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01180.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00935.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a09357 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a05296 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00935 ^ 1 * a02655 ^ 1)
theorem ha09357 : a09357.IsHomogeneous 1413 := by
  unfold a09357
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha05296.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00935.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a09358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09356 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09357 ^ 1)
theorem ha09358 : a09358.IsHomogeneous 1830 := by
  unfold a09358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09356.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09357.pow 1)))

@[irreducible]
def a09359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a04244 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a01180 ^ 1 * a02112 ^ 1)
theorem ha09359 : a09359.IsHomogeneous 2247 := by
  unfold a09359
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha04244.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha01180.pow 1)).mul (ha02112.pow 1)))

@[irreducible]
def a09360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09359 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09356 ^ 1)
theorem ha09360 : a09360.IsHomogeneous 2247 := by
  unfold a09360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09359.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09356.pow 1)))

@[irreducible]
def a09361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09360 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09358 ^ 1)
theorem ha09361 : a09361.IsHomogeneous 2247 := by
  unfold a09361
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09360.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09358.pow 1)))

@[irreducible]
def a09362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a09355 ^ 1) + (C ((25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a09361 ^ 1)
theorem ha09362 : a09362.IsHomogeneous 2309 := by
  unfold a09362
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha09355.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha09361.pow 1)))

@[irreducible]
def a09363 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a04249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07803 ^ 1)
theorem ha09363 : a09363.IsHomogeneous 2725 := by
  unfold a09363
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha04249.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07803.pow 1)))

@[irreducible]
def a09364 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02043 ^ 1 * a02115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a04249 ^ 1)
theorem ha09364 : a09364.IsHomogeneous 2368 := by
  unfold a09364
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02043.pow 1)).mul (ha02115.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha04249.pow 1)))

@[irreducible]
def a09365 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09364 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09363 ^ 1)
theorem ha09365 : a09365.IsHomogeneous 2725 := by
  unfold a09365
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09363.pow 1)))

@[irreducible]
def a09366 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01949 ^ 1)
theorem ha09366 : a09366.IsHomogeneous 1101 := by
  unfold a09366
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a09367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a02395 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a04858 ^ 1)
theorem ha09367 : a09367.IsHomogeneous 1374 := by
  unfold a09367
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha02395.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a09368 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09367 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09366 ^ 1)
theorem ha09368 : a09368.IsHomogeneous 1434 := by
  unfold a09368
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09367.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09366.pow 1)))

@[irreducible]
def a09369 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a02393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01034 ^ 1 * a01707 ^ 1)
theorem ha09369 : a09369.IsHomogeneous 922 := by
  unfold a09369
  exact (((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha02393.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01034.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a09370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a02393 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a04855 ^ 1)
theorem ha09370 : a09370.IsHomogeneous 1097 := by
  unfold a09370
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha02393.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha04855.pow 1)))

@[irreducible]
def a09371 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a09370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09369 ^ 1)
theorem ha09371 : a09371.IsHomogeneous 1176 := by
  unfold a09371
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha09370.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09369.pow 1)))

@[irreducible]
def a09372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a01034 ^ 1 * a01707 ^ 1)
theorem ha09372 : a09372.IsHomogeneous 747 := by
  unfold a09372
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha01034.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a09373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09372 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a09369 ^ 1)
theorem ha09373 : a09373.IsHomogeneous 1001 := by
  unfold a09373
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha09369.pow 1)))

@[irreducible]
def a09374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09373 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a09371 ^ 1)
theorem ha09374 : a09374.IsHomogeneous 1255 := by
  unfold a09374
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha09371.pow 1)))

@[irreducible]
def a09375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01033 ^ 1 * a01871 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a02391 ^ 1)
theorem ha09375 : a09375.IsHomogeneous 939 := by
  unfold a09375
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01033.pow 1)).mul (ha01871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha02391.pow 1)))

@[irreducible]
def a09376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a02391 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a04852 ^ 1)
theorem ha09376 : a09376.IsHomogeneous 685 := by
  unfold a09376
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha02391.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha04852.pow 1)))

@[irreducible]
def a09377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09375 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09376 ^ 1)
theorem ha09377 : a09377.IsHomogeneous 939 := by
  unfold a09377
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09375.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09376.pow 1)))

@[irreducible]
def a09378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00367 ^ 1 * a03851 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01033 ^ 1 * a01871 ^ 1)
theorem ha09378 : a09378.IsHomogeneous 1193 := by
  unfold a09378
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00367.pow 1)).mul (ha03851.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01033.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a09379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09378 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09375 ^ 1)
theorem ha09379 : a09379.IsHomogeneous 1193 := by
  unfold a09379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09378.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09375.pow 1)))

@[irreducible]
def a09380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09379 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09377 ^ 1)
theorem ha09380 : a09380.IsHomogeneous 1193 := by
  unfold a09380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09379.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09377.pow 1)))

@[irreducible]
def a09381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a02384 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01029 ^ 1 * a01877 ^ 1)
theorem ha09381 : a09381.IsHomogeneous 151 := by
  unfold a09381
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha02384.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01029.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a09382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a02384 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00293 ^ 1 * a04841 ^ 1)
theorem ha09382 : a09382.IsHomogeneous 151 := by
  unfold a09382
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha02384.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00293.pow 1)).mul (ha04841.pow 1)))

@[irreducible]
def a09383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09382 ^ 1)
theorem ha09383 : a09383.IsHomogeneous 151 := by
  unfold a09383
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09382.pow 1)))

@[irreducible]
def a09384 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a01029 ^ 1 * a01877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00365 ^ 1 * a03861 ^ 1)
theorem ha09384 : a09384.IsHomogeneous 145 := by
  unfold a09384
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha01029.pow 1)).mul (ha01877.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00365.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a09385 : Poly := (C ((-9 : ℂ) / (8 : ℂ)) * a09381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09384 ^ 1)
theorem ha09385 : a09385.IsHomogeneous 151 := by
  unfold a09385
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (8 : ℂ))).mul (ha09381.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09384.pow 1)))

@[irreducible]
def a09386 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a09385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09383 ^ 1)
theorem ha09386 : a09386.IsHomogeneous 151 := by
  unfold a09386
  exact (((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha09385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09383.pow 1)))

@[irreducible]
def a09387 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a03534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a03370 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a03562 ^ 1)
theorem ha09387 : a09387.IsHomogeneous 69 := by
  unfold a09387
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha03370.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha03562.pow 1)))

@[irreducible]
def a09388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00125 ^ 1 * a09387 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a04841 ^ 1)
theorem ha09388 : a09388.IsHomogeneous 145 := by
  unfold a09388
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha09387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha04841.pow 1)))

@[irreducible]
def a09389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09388 ^ 1) + (C ((81 : ℂ) / (4 : ℂ)) * a09382 ^ 1)
theorem ha09389 : a09389.IsHomogeneous 151 := by
  unfold a09389
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (4 : ℂ))).mul (ha09382.pow 1)))

@[irreducible]
def a09390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09383 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a09389 ^ 1)
theorem ha09390 : a09390.IsHomogeneous 151 := by
  unfold a09390
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha09389.pow 1)))

@[irreducible]
def a09391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09390 ^ 1)
theorem ha09391 : a09391.IsHomogeneous 151 := by
  unfold a09391
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09390.pow 1)))

@[irreducible]
def a09392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00713 ^ 1 * a02388 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01031 ^ 1 * a01703 ^ 1)
theorem ha09392 : a09392.IsHomogeneous 150 := by
  unfold a09392
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00713.pow 1)).mul (ha02388.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01031.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a09393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00713 ^ 1 * a02388 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00261 ^ 1 * a04848 ^ 1)
theorem ha09393 : a09393.IsHomogeneous 150 := by
  unfold a09393
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00713.pow 1)).mul (ha02388.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00261.pow 1)).mul (ha04848.pow 1)))

@[irreducible]
def a09394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09393 ^ 1)
theorem ha09394 : a09394.IsHomogeneous 150 := by
  unfold a09394
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09392.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09393.pow 1)))

@[irreducible]
def a09395 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a01031 ^ 1 * a01703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00366 ^ 1 * a03563 ^ 1)
theorem ha09395 : a09395.IsHomogeneous 144 := by
  unfold a09395
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha01031.pow 1)).mul (ha01703.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00366.pow 1)).mul (ha03563.pow 1)))

@[irreducible]
def a09396 : Poly := (C ((-15 : ℂ) / (16 : ℂ)) * a09392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09395 ^ 1)
theorem ha09396 : a09396.IsHomogeneous 150 := by
  unfold a09396
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (16 : ℂ))).mul (ha09392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09395.pow 1)))

@[irreducible]
def a09397 : Poly := (C ((-16 : ℂ) / (15 : ℂ)) * a09396 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09394 ^ 1)
theorem ha09397 : a09397.IsHomogeneous 150 := by
  unfold a09397
  exact (((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (15 : ℂ))).mul (ha09396.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09394.pow 1)))

@[irreducible]
def a09398 : Poly := (C ((-4 : ℂ) / (45 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00012 ^ 1 * a03534 ^ 1)
theorem ha09398 : a09398.IsHomogeneous 58 := by
  unfold a09398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (45 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha03562.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00012.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a09399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a09398 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a04848 ^ 1)
theorem ha09399 : a09399.IsHomogeneous 144 := by
  unfold a09399
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha09398.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha04848.pow 1)))

@[irreducible]
def a09400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09399 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a09393 ^ 1)
theorem ha09400 : a09400.IsHomogeneous 150 := by
  unfold a09400
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09399.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha09393.pow 1)))

@[irreducible]
def a09401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09394 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a09400 ^ 1)
theorem ha09401 : a09401.IsHomogeneous 150 := by
  unfold a09401
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09394.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha09400.pow 1)))

@[irreducible]
def a09402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09401 ^ 1)
theorem ha09402 : a09402.IsHomogeneous 150 := by
  unfold a09402
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09401.pow 1)))

@[irreducible]
def a09403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09391 ^ 1) + (C ((5 : ℂ) / (864 : ℂ)) * a00004 ^ 1 * a09402 ^ 1)
theorem ha09403 : a09403.IsHomogeneous 151 := by
  unfold a09403
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09391.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (864 : ℂ))).mul (ha00004.pow 1)).mul (ha09402.pow 1)))

@[irreducible]
def a09404 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09403 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a04852 ^ 1)
theorem ha09404 : a09404.IsHomogeneous 430 := by
  unfold a09404
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09403.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha04852.pow 1)))

@[irreducible]
def a09405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09376 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09404 ^ 1)
theorem ha09405 : a09405.IsHomogeneous 685 := by
  unfold a09405
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09376.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09404.pow 1)))

@[irreducible]
def a09406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09377 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09405 ^ 1)
theorem ha09406 : a09406.IsHomogeneous 939 := by
  unfold a09406
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09377.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09405.pow 1)))

@[irreducible]
def a09407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09380 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09406 ^ 1)
theorem ha09407 : a09407.IsHomogeneous 1193 := by
  unfold a09407
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09380.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09406.pow 1)))

@[irreducible]
def a09408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a04855 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a09407 ^ 1)
theorem ha09408 : a09408.IsHomogeneous 1272 := by
  unfold a09408
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha04855.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha09407.pow 1)))

@[irreducible]
def a09409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09370 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a09408 ^ 1)
theorem ha09409 : a09409.IsHomogeneous 1351 := by
  unfold a09409
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09370.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha09408.pow 1)))

@[irreducible]
def a09410 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a09409 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09371 ^ 1)
theorem ha09410 : a09410.IsHomogeneous 1430 := by
  unfold a09410
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha09409.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09371.pow 1)))

@[irreducible]
def a09411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09374 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a09410 ^ 1)
theorem ha09411 : a09411.IsHomogeneous 1509 := by
  unfold a09411
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09374.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha09410.pow 1)))

@[irreducible]
def a09412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a04858 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09411 ^ 1)
theorem ha09412 : a09412.IsHomogeneous 1617 := by
  unfold a09412
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha04858.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09411.pow 1)))

@[irreducible]
def a09413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09367 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a09412 ^ 1)
theorem ha09413 : a09413.IsHomogeneous 1707 := by
  unfold a09413
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09367.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09412.pow 1)))

@[irreducible]
def a09414 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09368 ^ 1)
theorem ha09414 : a09414.IsHomogeneous 1767 := by
  unfold a09414
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09413.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09368.pow 1)))

@[irreducible]
def a09415 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01035 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a03978 ^ 1)
theorem ha09415 : a09415.IsHomogeneous 828 := by
  unfold a09415
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01949.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a09416 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09366 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09415 ^ 1)
theorem ha09416 : a09416.IsHomogeneous 1161 := by
  unfold a09416
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09366.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09415.pow 1)))

@[irreducible]
def a09417 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09416 ^ 1)
theorem ha09417 : a09417.IsHomogeneous 1494 := by
  unfold a09417
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09368.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09416.pow 1)))

@[irreducible]
def a09418 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09417 ^ 1)
theorem ha09418 : a09418.IsHomogeneous 1827 := by
  unfold a09418
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09414.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09417.pow 1)))

@[irreducible]
def a09419 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01035 ^ 1 * a01979 ^ 1)
theorem ha09419 : a09419.IsHomogeneous 1029 := by
  unfold a09419
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01035.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a09420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a02395 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a04858 ^ 1)
theorem ha09420 : a09420.IsHomogeneous 1326 := by
  unfold a09420
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha02395.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a09421 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09419 ^ 1)
theorem ha09421 : a09421.IsHomogeneous 1362 := by
  unfold a09421
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09420.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09419.pow 1)))

@[irreducible]
def a09422 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09411 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a04858 ^ 1)
theorem ha09422 : a09422.IsHomogeneous 1593 := by
  unfold a09422
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09411.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a09423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09420 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a09422 ^ 1)
theorem ha09423 : a09423.IsHomogeneous 1659 := by
  unfold a09423
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09420.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09422.pow 1)))

@[irreducible]
def a09424 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09421 ^ 1)
theorem ha09424 : a09424.IsHomogeneous 1695 := by
  unfold a09424
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09423.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09421.pow 1)))

@[irreducible]
def a09425 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a01035 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a04032 ^ 1)
theorem ha09425 : a09425.IsHomogeneous 732 := by
  unfold a09425
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha01035.pow 1)).mul (ha01979.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a09426 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09425 ^ 1)
theorem ha09426 : a09426.IsHomogeneous 1065 := by
  unfold a09426
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09419.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09425.pow 1)))

@[irreducible]
def a09427 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09426 ^ 1)
theorem ha09427 : a09427.IsHomogeneous 1398 := by
  unfold a09427
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09421.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09426.pow 1)))

@[irreducible]
def a09428 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a09424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09427 ^ 1)
theorem ha09428 : a09428.IsHomogeneous 1731 := by
  unfold a09428
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha09424.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09427.pow 1)))

@[irreducible]
def a09429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01196 ^ 1 * a01290 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02687 ^ 1)
theorem ha09429 : a09429.IsHomogeneous 1452 := by
  unfold a09429
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01196.pow 1)).mul (ha01290.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a09430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02860 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01196 ^ 1 * a01290 ^ 1)
theorem ha09430 : a09430.IsHomogeneous 1179 := by
  unfold a09430
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02860.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01196.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a09431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09430 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09429 ^ 1)
theorem ha09431 : a09431.IsHomogeneous 1512 := by
  unfold a09431
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09430.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09429.pow 1)))

@[irreducible]
def a09432 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a05350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a02687 ^ 1)
theorem ha09432 : a09432.IsHomogeneous 1725 := by
  unfold a09432
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha05350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a09433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09429 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09432 ^ 1)
theorem ha09433 : a09433.IsHomogeneous 1785 := by
  unfold a09433
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09432.pow 1)))

@[irreducible]
def a09434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09431 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09433 ^ 1)
theorem ha09434 : a09434.IsHomogeneous 1845 := by
  unfold a09434
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09431.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09433.pow 1)))

@[irreducible]
def a09435 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a02860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a05627 ^ 1)
theorem ha09435 : a09435.IsHomogeneous 906 := by
  unfold a09435
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02860.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha05627.pow 1)))

@[irreducible]
def a09436 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09435 ^ 1)
theorem ha09436 : a09436.IsHomogeneous 1239 := by
  unfold a09436
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09430.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09435.pow 1)))

@[irreducible]
def a09437 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09436 ^ 1)
theorem ha09437 : a09437.IsHomogeneous 1572 := by
  unfold a09437
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09431.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09436.pow 1)))

@[irreducible]
def a09438 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09434 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09437 ^ 1)
theorem ha09438 : a09438.IsHomogeneous 1905 := by
  unfold a09438
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09434.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09437.pow 1)))

@[irreducible]
def a09439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01196 ^ 1 * a01313 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a02687 ^ 1)
theorem ha09439 : a09439.IsHomogeneous 1368 := by
  unfold a09439
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01196.pow 1)).mul (ha01313.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a09440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a02904 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a01196 ^ 1 * a01313 ^ 1)
theorem ha09440 : a09440.IsHomogeneous 1071 := by
  unfold a09440
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha02904.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha01196.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a09441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09440 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09439 ^ 1)
theorem ha09441 : a09441.IsHomogeneous 1404 := by
  unfold a09441
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09440.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09439.pow 1)))

@[irreducible]
def a09442 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a05350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a02687 ^ 1)
theorem ha09442 : a09442.IsHomogeneous 1665 := by
  unfold a09442
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha05350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a09443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09439 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a09442 ^ 1)
theorem ha09443 : a09443.IsHomogeneous 1701 := by
  unfold a09443
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09439.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha09442.pow 1)))

@[irreducible]
def a09444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09441 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09443 ^ 1)
theorem ha09444 : a09444.IsHomogeneous 1737 := by
  unfold a09444
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09443.pow 1)))

@[irreducible]
def a09445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a05699 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a02904 ^ 1)
theorem ha09445 : a09445.IsHomogeneous 774 := by
  unfold a09445
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha05699.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02904.pow 1)))

@[irreducible]
def a09446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09445 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09440 ^ 1)
theorem ha09446 : a09446.IsHomogeneous 1107 := by
  unfold a09446
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09445.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09440.pow 1)))

@[irreducible]
def a09447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09446 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09441 ^ 1)
theorem ha09447 : a09447.IsHomogeneous 1440 := by
  unfold a09447
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09446.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09441.pow 1)))

@[irreducible]
def a09448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09447 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09444 ^ 1)
theorem ha09448 : a09448.IsHomogeneous 1773 := by
  unfold a09448
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09447.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09444.pow 1)))

@[irreducible]
def a09449 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01103 ^ 1 * a01886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02540 ^ 1)
theorem ha09449 : a09449.IsHomogeneous 1507 := by
  unfold a09449
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01103.pow 1)).mul (ha01886.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02540.pow 1)))

@[irreducible]
def a09450 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a02540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a05118 ^ 1)
theorem ha09450 : a09450.IsHomogeneous 1234 := by
  unfold a09450
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02540.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha05118.pow 1)))

@[irreducible]
def a09451 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09450 ^ 1)
theorem ha09451 : a09451.IsHomogeneous 1567 := by
  unfold a09451
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09449.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09450.pow 1)))

@[irreducible]
def a09452 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01103 ^ 1 * a01886 ^ 1)
theorem ha09452 : a09452.IsHomogeneous 1780 := by
  unfold a09452
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01103.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a09453 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09449 ^ 1)
theorem ha09453 : a09453.IsHomogeneous 1840 := by
  unfold a09453
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09452.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09449.pow 1)))

@[irreducible]
def a09454 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09451 ^ 1)
theorem ha09454 : a09454.IsHomogeneous 1900 := by
  unfold a09454
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09453.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09451.pow 1)))

@[irreducible]
def a09455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02538 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01102 ^ 1 * a01946 ^ 1)
theorem ha09455 : a09455.IsHomogeneous 499 := by
  unfold a09455
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02538.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01102.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a09456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a05115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02538 ^ 1)
theorem ha09456 : a09456.IsHomogeneous 499 := by
  unfold a09456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha05115.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02538.pow 1)))

@[irreducible]
def a09457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09456 ^ 1)
theorem ha09457 : a09457.IsHomogeneous 499 := by
  unfold a09457
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09456.pow 1)))

@[irreducible]
def a09458 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a01102 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00398 ^ 1 * a03974 ^ 1)
theorem ha09458 : a09458.IsHomogeneous 499 := by
  unfold a09458
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha01102.pow 1)).mul (ha01946.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00398.pow 1)).mul (ha03974.pow 1)))

@[irreducible]
def a09459 : Poly := (C ((-36 : ℂ) / (1 : ℂ)) * a09458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09455 ^ 1)
theorem ha09459 : a09459.IsHomogeneous 499 := by
  unfold a09459
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (1 : ℂ))).mul (ha09458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09455.pow 1)))

@[irreducible]
def a09460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09459 ^ 1)
theorem ha09460 : a09460.IsHomogeneous 499 := by
  unfold a09460
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09459.pow 1)))

@[irreducible]
def a09461 : Poly := (C ((-54 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01041 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a02413 ^ 1)
theorem ha09461 : a09461.IsHomogeneous 138 := by
  unfold a09461
  exact (((((isHomogeneous_C (σ := Fin 6) ((-54 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01041.pow 1)).mul (ha01923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09462 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00303 ^ 1 * a04894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a02413 ^ 1)
theorem ha09462 : a09462.IsHomogeneous 138 := by
  unfold a09462
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha04894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a09463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09462 ^ 1)
theorem ha09463 : a09463.IsHomogeneous 138 := by
  unfold a09463
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09462.pow 1)))

@[irreducible]
def a09464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha09464 : a09464.IsHomogeneous 12 := by
  unfold a09464
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a09465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01401 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a09464 ^ 1)
theorem ha09465 : a09465.IsHomogeneous 12 := by
  unfold a09465
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha09464.pow 1)))

@[irreducible]
def a09466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a01327 ^ 1)
theorem ha09466 : a09466.IsHomogeneous 12 := by
  unfold a09466
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a09467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09464 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a09466 ^ 1)
theorem ha09467 : a09467.IsHomogeneous 12 := by
  unfold a09467
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha09466.pow 1)))

@[irreducible]
def a09468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09465 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a09467 ^ 1)
theorem ha09468 : a09468.IsHomogeneous 12 := by
  unfold a09468
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha09467.pow 1)))

@[irreducible]
def a09469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01403 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09465 ^ 1)
theorem ha09469 : a09469.IsHomogeneous 12 := by
  unfold a09469
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01403.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09465.pow 1)))

@[irreducible]
def a09470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09468 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09469 ^ 1)
theorem ha09470 : a09470.IsHomogeneous 12 := by
  unfold a09470
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09468.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09469.pow 1)))

@[irreducible]
def a09471 : Poly := (C ((-21 : ℂ) / (2 : ℂ)) * a09470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03172 ^ 1)
theorem ha09471 : a09471.IsHomogeneous 12 := by
  unfold a09471
  exact (((isHomogeneous_C (σ := Fin 6) ((-21 : ℂ) / (2 : ℂ))).mul (ha09470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03172.pow 1)))

end CycleQ2Concrete
