import Proposal.CurrentAtoms040

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a12288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12286 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a12287 ^ 1)
theorem ha12288 : a12288.IsHomogeneous 42 := by
  unfold a12288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha12287.pow 1)))

@[irreducible]
def a12289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00721 ^ 1 * a03597 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 5 * a01721 ^ 2)
theorem ha12289 : a12289.IsHomogeneous 43 := by
  unfold a12289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00721.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 5)).mul (ha01721.pow 2)))

@[irreducible]
def a12290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a06781 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a03597 ^ 1)
theorem ha12290 : a12290.IsHomogeneous 44 := by
  unfold a12290
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha06781.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha03597.pow 1)))

@[irreducible]
def a12291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12290 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12289 ^ 1)
theorem ha12291 : a12291.IsHomogeneous 44 := by
  unfold a12291
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12290.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12289.pow 1)))

@[irreducible]
def a12292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12291 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12289 ^ 1)
theorem ha12292 : a12292.IsHomogeneous 44 := by
  unfold a12292
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12291.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12289.pow 1)))

@[irreducible]
def a12293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a10809 ^ 1) + (C ((7 : ℂ) / (36 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1)
theorem ha12293 : a12293.IsHomogeneous 19 := by
  unfold a12293
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha10809.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (36 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a12294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a12293 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a06781 ^ 1)
theorem ha12294 : a12294.IsHomogeneous 44 := by
  unfold a12294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha12293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha06781.pow 1)))

@[irreducible]
def a12295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12290 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12294 ^ 1)
theorem ha12295 : a12295.IsHomogeneous 44 := by
  unfold a12295
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12294.pow 1)))

@[irreducible]
def a12296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12295 ^ 1)
theorem ha12296 : a12296.IsHomogeneous 44 := by
  unfold a12296
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12295.pow 1)))

@[irreducible]
def a12297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12296 ^ 1)
theorem ha12297 : a12297.IsHomogeneous 44 := by
  unfold a12297
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12296.pow 1)))

@[irreducible]
def a12298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12292 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12297 ^ 1)
theorem ha12298 : a12298.IsHomogeneous 44 := by
  unfold a12298
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12297.pow 1)))

@[irreducible]
def a12299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a12298 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a12288 ^ 1)
theorem ha12299 : a12299.IsHomogeneous 49 := by
  unfold a12299
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha12298.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha12288.pow 1)))

@[irreducible]
def a12300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a06786 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a12299 ^ 1)
theorem ha12300 : a12300.IsHomogeneous 104 := by
  unfold a12300
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha06786.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha12299.pow 1)))

@[irreducible]
def a12301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00105 ^ 1 * a12300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12270 ^ 1)
theorem ha12301 : a12301.IsHomogeneous 162 := by
  unfold a12301
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00105.pow 1)).mul (ha12300.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12270.pow 1)))

@[irreducible]
def a12302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12271 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a12301 ^ 1)
theorem ha12302 : a12302.IsHomogeneous 162 := by
  unfold a12302
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12271.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha12301.pow 1)))

@[irreducible]
def a12303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12302 ^ 1)
theorem ha12303 : a12303.IsHomogeneous 162 := by
  unfold a12303
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12302.pow 1)))

@[irreducible]
def a12304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12276 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12303 ^ 1)
theorem ha12304 : a12304.IsHomogeneous 162 := by
  unfold a12304
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12276.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12303.pow 1)))

@[irreducible]
def a12305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00117 ^ 1 * a12304 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00270 ^ 1 * a06790 ^ 1)
theorem ha12305 : a12305.IsHomogeneous 187 := by
  unfold a12305
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00117.pow 1)).mul (ha12304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00270.pow 1)).mul (ha06790.pow 1)))

@[irreducible]
def a12306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12260 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a12305 ^ 1)
theorem ha12306 : a12306.IsHomogeneous 187 := by
  unfold a12306
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha12305.pow 1)))

@[irreducible]
def a12307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12306 ^ 1)
theorem ha12307 : a12307.IsHomogeneous 187 := by
  unfold a12307
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12261.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12306.pow 1)))

@[irreducible]
def a12308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12307 ^ 1)
theorem ha12308 : a12308.IsHomogeneous 187 := by
  unfold a12308
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12307.pow 1)))

@[irreducible]
def a12309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12308 ^ 1)
theorem ha12309 : a12309.IsHomogeneous 187 := by
  unfold a12309
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12308.pow 1)))

@[irreducible]
def a12310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a08025 ^ 1)
theorem ha12310 : a12310.IsHomogeneous 15 := by
  unfold a12310
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha08025.pow 1)))

@[irreducible]
def a12311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12310 ^ 1)
theorem ha12311 : a12311.IsHomogeneous 15 := by
  unfold a12311
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12310.pow 1)))

@[irreducible]
def a12312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12311 ^ 1)
theorem ha12312 : a12312.IsHomogeneous 15 := by
  unfold a12312
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12311.pow 1)))

@[irreducible]
def a12313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12312 ^ 1)
theorem ha12313 : a12313.IsHomogeneous 15 := by
  unfold a12313
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12312.pow 1)))

@[irreducible]
def a12314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12313 ^ 1)
theorem ha12314 : a12314.IsHomogeneous 15 := by
  unfold a12314
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12313.pow 1)))

@[irreducible]
def a12315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12314 ^ 1)
theorem ha12315 : a12315.IsHomogeneous 15 := by
  unfold a12315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01732.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12314.pow 1)))

@[irreducible]
def a12316 : Poly := (C ((-432 : ℂ) / (7 : ℂ)) * a00005 ^ 3 * a12315 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00108 ^ 1)
theorem ha12316 : a12316.IsHomogeneous 18 := by
  unfold a12316
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (7 : ℂ))).mul (ha00005.pow 3)).mul (ha12315.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00108.pow 1)))

@[irreducible]
def a12317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a03608 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00105 ^ 1 * a12316 ^ 1)
theorem ha12317 : a12317.IsHomogeneous 73 := by
  unfold a12317
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha03608.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00105.pow 1)).mul (ha12316.pow 1)))

@[irreducible]
def a12318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03608 ^ 1 * a12263 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a12317 ^ 1)
theorem ha12318 : a12318.IsHomogeneous 128 := by
  unfold a12318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03608.pow 1)).mul (ha12263.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha12317.pow 1)))

@[irreducible]
def a12319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a12318 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12264 ^ 1)
theorem ha12319 : a12319.IsHomogeneous 187 := by
  unfold a12319
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha12318.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12264.pow 1)))

@[irreducible]
def a12320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12265 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a12319 ^ 1)
theorem ha12320 : a12320.IsHomogeneous 187 := by
  unfold a12320
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha12319.pow 1)))

@[irreducible]
def a12321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12320 ^ 1)
theorem ha12321 : a12321.IsHomogeneous 187 := by
  unfold a12321
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12320.pow 1)))

@[irreducible]
def a12322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12321 ^ 1)
theorem ha12322 : a12322.IsHomogeneous 187 := by
  unfold a12322
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12309.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12321.pow 1)))

@[irreducible]
def a12323 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12322 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a06799 ^ 1)
theorem ha12323 : a12323.IsHomogeneous 333 := by
  unfold a12323
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12322.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha06799.pow 1)))

@[irreducible]
def a12324 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12323 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12250 ^ 1)
theorem ha12324 : a12324.IsHomogeneous 479 := by
  unfold a12324
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12250.pow 1)))

@[irreducible]
def a12325 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12251 ^ 1)
theorem ha12325 : a12325.IsHomogeneous 624 := by
  unfold a12325
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12251.pow 1)))

@[irreducible]
def a12326 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12325 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12252 ^ 1)
theorem ha12326 : a12326.IsHomogeneous 769 := by
  unfold a12326
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12252.pow 1)))

@[irreducible]
def a12327 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12326 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12256 ^ 1)
theorem ha12327 : a12327.IsHomogeneous 914 := by
  unfold a12327
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12256.pow 1)))

@[irreducible]
def a12328 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01742 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01825 ^ 1 * a03620 ^ 1)
theorem ha12328 : a12328.IsHomogeneous 620 := by
  unfold a12328
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01742.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01825.pow 1)).mul (ha03620.pow 1)))

@[irreducible]
def a12329 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1 * a03620 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a06816 ^ 1)
theorem ha12329 : a12329.IsHomogeneous 766 := by
  unfold a12329
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).mul (ha03620.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha06816.pow 1)))

@[irreducible]
def a12330 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12329 ^ 1)
theorem ha12330 : a12330.IsHomogeneous 766 := by
  unfold a12330
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12329.pow 1)))

@[irreducible]
def a12331 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a07053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01742 ^ 1 * a03768 ^ 1)
theorem ha12331 : a12331.IsHomogeneous 474 := by
  unfold a12331
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha07053.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01742.pow 1)).mul (ha03768.pow 1)))

@[irreducible]
def a12332 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12331 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12328 ^ 1)
theorem ha12332 : a12332.IsHomogeneous 620 := by
  unfold a12332
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12331.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12328.pow 1)))

@[irreducible]
def a12333 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12330 ^ 1)
theorem ha12333 : a12333.IsHomogeneous 766 := by
  unfold a12333
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12330.pow 1)))

@[irreducible]
def a12334 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01825 ^ 1 * a03617 ^ 1)
theorem ha12334 : a12334.IsHomogeneous 475 := by
  unfold a12334
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01825.pow 1)).mul (ha03617.pow 1)))

@[irreducible]
def a12335 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1 * a03617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a06811 ^ 1)
theorem ha12335 : a12335.IsHomogeneous 621 := by
  unfold a12335
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).mul (ha03617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha06811.pow 1)))

@[irreducible]
def a12336 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12335 ^ 1)
theorem ha12336 : a12336.IsHomogeneous 621 := by
  unfold a12336
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12335.pow 1)))

@[irreducible]
def a12337 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03768 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a01825 ^ 1)
theorem ha12337 : a12337.IsHomogeneous 330 := by
  unfold a12337
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03768.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha01825.pow 1)))

@[irreducible]
def a12338 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00775 ^ 1 * a06809 ^ 1)
theorem ha12338 : a12338.IsHomogeneous 476 := by
  unfold a12338
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00775.pow 1)).mul (ha06809.pow 1)))

@[irreducible]
def a12339 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12338 ^ 1)
theorem ha12339 : a12339.IsHomogeneous 476 := by
  unfold a12339
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12338.pow 1)))

@[irreducible]
def a12340 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01825 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a00775 ^ 1)
theorem ha12340 : a12340.IsHomogeneous 331 := by
  unfold a12340
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01825.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha00775.pow 1)))

@[irreducible]
def a12341 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 2)
theorem ha12341 : a12341.IsHomogeneous 290 := by
  unfold a12341
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 2)))

@[irreducible]
def a12342 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12341 ^ 1)
theorem ha12342 : a12342.IsHomogeneous 290 := by
  unfold a12342
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12341.pow 1)))

@[irreducible]
def a12343 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a12342 ^ 1)
theorem ha12343 : a12343.IsHomogeneous 435 := by
  unfold a12343
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha12342.pow 1)))

@[irreducible]
def a12344 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a06809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a12343 ^ 1)
theorem ha12344 : a12344.IsHomogeneous 580 := by
  unfold a12344
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha06809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha12343.pow 1)))

@[irreducible]
def a12345 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12338 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12344 ^ 1)
theorem ha12345 : a12345.IsHomogeneous 580 := by
  unfold a12345
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12338.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12344.pow 1)))

@[irreducible]
def a12346 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12345 ^ 1)
theorem ha12346 : a12346.IsHomogeneous 580 := by
  unfold a12346
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12339.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12345.pow 1)))

@[irreducible]
def a12347 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a06811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a12346 ^ 1)
theorem ha12347 : a12347.IsHomogeneous 725 := by
  unfold a12347
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha06811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha12346.pow 1)))

@[irreducible]
def a12348 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12347 ^ 1)
theorem ha12348 : a12348.IsHomogeneous 725 := by
  unfold a12348
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12347.pow 1)))

@[irreducible]
def a12349 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12336 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12348 ^ 1)
theorem ha12349 : a12349.IsHomogeneous 725 := by
  unfold a12349
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12336.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12348.pow 1)))

@[irreducible]
def a12350 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a07053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a03768 ^ 1)
theorem ha12350 : a12350.IsHomogeneous 329 := by
  unfold a12350
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07053.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha03768.pow 1)))

@[irreducible]
def a12351 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12334 ^ 1)
theorem ha12351 : a12351.IsHomogeneous 475 := by
  unfold a12351
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12334.pow 1)))

@[irreducible]
def a12352 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12351 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12336 ^ 1)
theorem ha12352 : a12352.IsHomogeneous 621 := by
  unfold a12352
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12351.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12336.pow 1)))

@[irreducible]
def a12353 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12349 ^ 1)
theorem ha12353 : a12353.IsHomogeneous 725 := by
  unfold a12353
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12349.pow 1)))

@[irreducible]
def a12354 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a00775 ^ 1 * a06816 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a12353 ^ 1)
theorem ha12354 : a12354.IsHomogeneous 870 := by
  unfold a12354
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00775.pow 1)).mul (ha06816.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha12353.pow 1)))

@[irreducible]
def a12355 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12354 ^ 1)
theorem ha12355 : a12355.IsHomogeneous 870 := by
  unfold a12355
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12354.pow 1)))

@[irreducible]
def a12356 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12355 ^ 1)
theorem ha12356 : a12356.IsHomogeneous 870 := by
  unfold a12356
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12355.pow 1)))

@[irreducible]
def a12357 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12356 ^ 1)
theorem ha12357 : a12357.IsHomogeneous 870 := by
  unfold a12357
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12356.pow 1)))

@[irreducible]
def a12358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00737 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00285 ^ 1 * a01750 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00737 ^ 1 * a00773 ^ 1)
theorem ha12358 : a12358.IsHomogeneous 179 := by
  unfold a12358
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00285.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00737.pow 1)).mul (ha00773.pow 1)))

@[irreducible]
def a12359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00737 ^ 1 * a00773 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a01822 ^ 1)
theorem ha12359 : a12359.IsHomogeneous 178 := by
  unfold a12359
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00737.pow 1)).mul (ha00773.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a00773 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00737 ^ 1)
theorem ha12360 : a12360.IsHomogeneous 179 := by
  unfold a12360
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00773.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a12361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12358 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12360 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a12359 ^ 1)
theorem ha12361 : a12361.IsHomogeneous 179 := by
  unfold a12361
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12360.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha12359.pow 1)))

@[irreducible]
def a12362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00737 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00737 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01750 ^ 1)
theorem ha12362 : a12362.IsHomogeneous 179 := by
  unfold a12362
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00737.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a12363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03639 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a01750 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00285 ^ 1 * a01750 ^ 1)
theorem ha12363 : a12363.IsHomogeneous 178 := by
  unfold a12363
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03639.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha01750.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00285.pow 1)).mul (ha01750.pow 1)))

@[irreducible]
def a12364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12358 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12362 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a12363 ^ 1)
theorem ha12364 : a12364.IsHomogeneous 179 := by
  unfold a12364
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12362.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha12363.pow 1)))

@[irreducible]
def a12365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a00262 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a00285 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00737 ^ 1)
theorem ha12365 : a12365.IsHomogeneous 179 := by
  unfold a12365
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha00285.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00737.pow 1)))

@[irreducible]
def a12366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12362 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a12365 ^ 1)
theorem ha12366 : a12366.IsHomogeneous 179 := by
  unfold a12366
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12360.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12362.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha12365.pow 1)))

@[irreducible]
def a12367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12361 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12364 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12366 ^ 1)
theorem ha12367 : a12367.IsHomogeneous 179 := by
  unfold a12367
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12364.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12366.pow 1)))

@[irreducible]
def a12368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00773 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00773 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a01822 ^ 1)
theorem ha12368 : a12368.IsHomogeneous 138 := by
  unfold a12368
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a03764 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a01822 ^ 1)
theorem ha12369 : a12369.IsHomogeneous 137 := by
  unfold a12369
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01822.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha03764.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12368 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12359 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a12369 ^ 1)
theorem ha12370 : a12370.IsHomogeneous 180 := by
  unfold a12370
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12359.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha12369.pow 1)))

@[irreducible]
def a12371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00773 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00285 ^ 1)
theorem ha12371 : a12371.IsHomogeneous 139 := by
  unfold a12371
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00773.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00285.pow 1)))

@[irreducible]
def a12372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12371 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a12368 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12360 ^ 1)
theorem ha12372 : a12372.IsHomogeneous 181 := by
  unfold a12372
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12371.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha12368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12360.pow 1)))

@[irreducible]
def a12373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12372 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12370 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12361 ^ 1)
theorem ha12373 : a12373.IsHomogeneous 181 := by
  unfold a12373
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12370.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12361.pow 1)))

@[irreducible]
def a12374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00285 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00123 ^ 1 * a00262 ^ 1)
theorem ha12374 : a12374.IsHomogeneous 139 := by
  unfold a12374
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00123.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12371 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00103 ^ 1 * a12374 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12365 ^ 1)
theorem ha12375 : a12375.IsHomogeneous 181 := by
  unfold a12375
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12371.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00103.pow 1)).mul (ha12374.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12365.pow 1)))

@[irreducible]
def a12376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12375 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12366 ^ 1)
theorem ha12376 : a12376.IsHomogeneous 181 := by
  unfold a12376
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12372.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12375.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12366.pow 1)))

@[irreducible]
def a12377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12376 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12367 ^ 1)
theorem ha12377 : a12377.IsHomogeneous 181 := by
  unfold a12377
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12373.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12376.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12367.pow 1)))

@[irreducible]
def a12378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00737 ^ 1 * a00773 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00773 ^ 1 * a01750 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00003 ^ 1 * a00737 ^ 1 * a01822 ^ 1)
theorem ha12378 : a12378.IsHomogeneous 178 := by
  unfold a12378
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00737.pow 1)).mul (ha00773.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00773.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00003.pow 1)).mul (ha00737.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00773 ^ 1 * a01750 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01750 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00285 ^ 1 * a03639 ^ 1)
theorem ha12379 : a12379.IsHomogeneous 178 := by
  unfold a12379
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00773.pow 1)).mul (ha01750.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01750.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00285.pow 1)).mul (ha03639.pow 1)))

@[irreducible]
def a12380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12358 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12379 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a12378 ^ 1)
theorem ha12380 : a12380.IsHomogeneous 179 := by
  unfold a12380
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12358.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12379.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha12378.pow 1)))

@[irreducible]
def a12381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a03764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00262 ^ 1 * a01822 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00737 ^ 1 * a01822 ^ 1)
theorem ha12381 : a12381.IsHomogeneous 177 := by
  unfold a12381
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha03764.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha01822.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00737.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12359 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12378 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a12381 ^ 1)
theorem ha12382 : a12382.IsHomogeneous 178 := by
  unfold a12382
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12378.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha12381.pow 1)))

@[irreducible]
def a12383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12361 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12380 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a12382 ^ 1)
theorem ha12383 : a12383.IsHomogeneous 179 := by
  unfold a12383
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12380.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha12382.pow 1)))

@[irreducible]
def a12384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03639 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a06851 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00285 ^ 1 * a03639 ^ 1)
theorem ha12384 : a12384.IsHomogeneous 177 := by
  unfold a12384
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03639.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha06851.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00285.pow 1)).mul (ha03639.pow 1)))

@[irreducible]
def a12385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12363 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12379 ^ 1)
theorem ha12385 : a12385.IsHomogeneous 178 := by
  unfold a12385
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12363.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12379.pow 1)))

@[irreducible]
def a12386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12364 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12380 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a12385 ^ 1)
theorem ha12386 : a12386.IsHomogeneous 179 := by
  unfold a12386
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12380.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha12385.pow 1)))

@[irreducible]
def a12387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12367 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12383 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12386 ^ 1)
theorem ha12387 : a12387.IsHomogeneous 179 := by
  unfold a12387
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12367.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12383.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12386.pow 1)))

@[irreducible]
def a12388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a03764 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a07048 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a03764 ^ 1)
theorem ha12388 : a12388.IsHomogeneous 136 := by
  unfold a12388
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha03764.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha07048.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a12389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12369 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a12388 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12381 ^ 1)
theorem ha12389 : a12389.IsHomogeneous 179 := by
  unfold a12389
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12369.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha12388.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12381.pow 1)))

@[irreducible]
def a12390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12370 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12382 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a12389 ^ 1)
theorem ha12390 : a12390.IsHomogeneous 180 := by
  unfold a12390
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12370.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12382.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha12389.pow 1)))

@[irreducible]
def a12391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12373 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a12390 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12383 ^ 1)
theorem ha12391 : a12391.IsHomogeneous 181 := by
  unfold a12391
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha12390.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12383.pow 1)))

@[irreducible]
def a12392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12377 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12391 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12387 ^ 1)
theorem ha12392 : a12392.IsHomogeneous 181 := by
  unfold a12392
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12391.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12387.pow 1)))

@[irreducible]
def a12393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00773 ^ 1 * a01750 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00773 ^ 1 * a03639 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01750 ^ 1 * a01822 ^ 1)
theorem ha12393 : a12393.IsHomogeneous 182 := by
  unfold a12393
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00773.pow 1)).mul (ha01750.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00773.pow 1)).mul (ha03639.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01750.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a12394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00737 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01750 ^ 1 * a01822 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a03764 ^ 1)
theorem ha12394 : a12394.IsHomogeneous 182 := by
  unfold a12394
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00737.pow 1)).mul (ha01822.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01750.pow 1)).mul (ha01822.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a12395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12378 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12393 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a12394 ^ 1)
theorem ha12395 : a12395.IsHomogeneous 182 := by
  unfold a12395
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12378.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12393.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha12394.pow 1)))

@[irreducible]
def a12396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00285 ^ 1 * a03639 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a06851 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00773 ^ 1 * a03639 ^ 1)
theorem ha12396 : a12396.IsHomogeneous 182 := by
  unfold a12396
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00285.pow 1)).mul (ha03639.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha06851.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00773.pow 1)).mul (ha03639.pow 1)))

@[irreducible]
def a12397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12393 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12396 ^ 1)
theorem ha12397 : a12397.IsHomogeneous 182 := by
  unfold a12397
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12393.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12396.pow 1)))

@[irreducible]
def a12398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12380 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12397 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a12395 ^ 1)
theorem ha12398 : a12398.IsHomogeneous 182 := by
  unfold a12398
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12397.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha12395.pow 1)))

@[irreducible]
def a12399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00262 ^ 1 * a07048 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00262 ^ 1 * a03764 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00737 ^ 1 * a03764 ^ 1)
theorem ha12399 : a12399.IsHomogeneous 182 := by
  unfold a12399
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha07048.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00262.pow 1)).mul (ha03764.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00737.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a12400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12381 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a12399 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a12394 ^ 1)
theorem ha12400 : a12400.IsHomogeneous 182 := by
  unfold a12400
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha12399.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha12394.pow 1)))

@[irreducible]
def a12401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12382 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12395 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a12400 ^ 1)
theorem ha12401 : a12401.IsHomogeneous 182 := by
  unfold a12401
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12382.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12395.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha12400.pow 1)))

@[irreducible]
def a12402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12383 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12398 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a12401 ^ 1)
theorem ha12402 : a12402.IsHomogeneous 182 := by
  unfold a12402
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12398.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha12401.pow 1)))

@[irreducible]
def a12403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00717 ^ 1 * a03590 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a01716 ^ 2)
theorem ha12403 : a12403.IsHomogeneous 78 := by
  unfold a12403
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00717.pow 1)).mul (ha03590.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha01716.pow 2)))

@[irreducible]
def a12404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a06772 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00717 ^ 1 * a03590 ^ 1)
theorem ha12404 : a12404.IsHomogeneous 76 := by
  unfold a12404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00717.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12404 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12403 ^ 1)
theorem ha12405 : a12405.IsHomogeneous 78 := by
  unfold a12405
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12403.pow 1)))

@[irreducible]
def a12406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12403 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12405 ^ 1)
theorem ha12406 : a12406.IsHomogeneous 78 := by
  unfold a12406
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12403.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12405.pow 1)))

@[irreducible]
def a12407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a06772 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a12281 ^ 1)
theorem ha12407 : a12407.IsHomogeneous 78 := by
  unfold a12407
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha12281.pow 1)))

@[irreducible]
def a12408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12407 ^ 1)
theorem ha12408 : a12408.IsHomogeneous 78 := by
  unfold a12408
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12407.pow 1)))

@[irreducible]
def a12409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12405 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12408 ^ 1)
theorem ha12409 : a12409.IsHomogeneous 78 := by
  unfold a12409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12405.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12408.pow 1)))

@[irreducible]
def a12410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12406 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12409 ^ 1)
theorem ha12410 : a12410.IsHomogeneous 78 := by
  unfold a12410
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12409.pow 1)))

@[irreducible]
def a12411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12406 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12410 ^ 1)
theorem ha12411 : a12411.IsHomogeneous 78 := by
  unfold a12411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12410.pow 1)))

@[irreducible]
def a12412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a12411 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00123 ^ 1 * a06851 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a06851 ^ 1)
theorem ha12412 : a12412.IsHomogeneous 182 := by
  unfold a12412
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha12411.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00123.pow 1)).mul (ha06851.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha06851.pow 1)))

@[irreducible]
def a12413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12412 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a12396 ^ 1)
theorem ha12413 : a12413.IsHomogeneous 182 := by
  unfold a12413
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12412.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha12396.pow 1)))

@[irreducible]
def a12414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a12385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12413 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12397 ^ 1)
theorem ha12414 : a12414.IsHomogeneous 182 := by
  unfold a12414
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha12385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12413.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12397.pow 1)))

@[irreducible]
def a12415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12398 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a12414 ^ 1)
theorem ha12415 : a12415.IsHomogeneous 182 := by
  unfold a12415
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12398.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha12414.pow 1)))

@[irreducible]
def a12416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12415 ^ 1)
theorem ha12416 : a12416.IsHomogeneous 182 := by
  unfold a12416
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12402.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12415.pow 1)))

@[irreducible]
def a12417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00751 ^ 1 * a03686 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01776 ^ 1 * a01779 ^ 1)
theorem ha12417 : a12417.IsHomogeneous 87 := by
  unfold a12417
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00751.pow 1)).mul (ha03686.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01776.pow 1)).mul (ha01779.pow 1)))

@[irreducible]
def a12418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00749 ^ 1 * a03690 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a01776 ^ 1 * a01779 ^ 1)
theorem ha12418 : a12418.IsHomogeneous 87 := by
  unfold a12418
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00749.pow 1)).mul (ha03690.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha01776.pow 1)).mul (ha01779.pow 1)))

@[irreducible]
def a12419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12417 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12418 ^ 1)
theorem ha12419 : a12419.IsHomogeneous 87 := by
  unfold a12419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12418.pow 1)))

@[irreducible]
def a12420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00276 ^ 1 * a06926 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00751 ^ 1 * a03686 ^ 1)
theorem ha12420 : a12420.IsHomogeneous 87 := by
  unfold a12420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00276.pow 1)).mul (ha06926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00751.pow 1)).mul (ha03686.pow 1)))

@[irreducible]
def a12421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12417 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12420 ^ 1)
theorem ha12421 : a12421.IsHomogeneous 87 := by
  unfold a12421
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12420.pow 1)))

@[irreducible]
def a12422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12421 ^ 1)
theorem ha12422 : a12422.IsHomogeneous 87 := by
  unfold a12422
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12421.pow 1)))

@[irreducible]
def a12423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00275 ^ 1 * a06931 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00749 ^ 1 * a03690 ^ 1)
theorem ha12423 : a12423.IsHomogeneous 86 := by
  unfold a12423
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00275.pow 1)).mul (ha06931.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00749.pow 1)).mul (ha03690.pow 1)))

@[irreducible]
def a12424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12423 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12418 ^ 1)
theorem ha12424 : a12424.IsHomogeneous 87 := by
  unfold a12424
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12418.pow 1)))

@[irreducible]
def a12425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12419 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12424 ^ 1)
theorem ha12425 : a12425.IsHomogeneous 87 := by
  unfold a12425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12424.pow 1)))

@[irreducible]
def a12426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12425 ^ 1)
theorem ha12426 : a12426.IsHomogeneous 87 := by
  unfold a12426
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12425.pow 1)))

@[irreducible]
def a12427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00717 ^ 1)
theorem ha12427 : a12427.IsHomogeneous 46 := by
  unfold a12427
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00717.pow 1)))

@[irreducible]
def a12428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00717 ^ 1)
theorem ha12428 : a12428.IsHomogeneous 40 := by
  unfold a12428
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a12429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00262 ^ 1)
theorem ha12429 : a12429.IsHomogeneous 46 := by
  unfold a12429
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)))

@[irreducible]
def a12430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12427 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12429 ^ 1) + (C ((63 : ℂ) / (20 : ℂ)) * a00003 ^ 6 * a12428 ^ 1)
theorem ha12430 : a12430.IsHomogeneous 46 := by
  unfold a12430
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12427.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12429.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((63 : ℂ) / (20 : ℂ))).mul (ha00003.pow 6)).mul (ha12428.pow 1)))

@[irreducible]
def a12431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a01716 ^ 1)
theorem ha12431 : a12431.IsHomogeneous 46 := by
  unfold a12431
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a03590 ^ 1)
theorem ha12432 : a12432.IsHomogeneous 45 := by
  unfold a12432
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12427 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12432 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12431 ^ 1)
theorem ha12433 : a12433.IsHomogeneous 46 := by
  unfold a12433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12427.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12432.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12431.pow 1)))

@[irreducible]
def a12434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1)
theorem ha12434 : a12434.IsHomogeneous 46 := by
  unfold a12434
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12429 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12434 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12431 ^ 1)
theorem ha12435 : a12435.IsHomogeneous 46 := by
  unfold a12435
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12429.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12434.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12431.pow 1)))

@[irreducible]
def a12436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12433 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12435 ^ 1)
theorem ha12436 : a12436.IsHomogeneous 46 := by
  unfold a12436
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12430.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12433.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12435.pow 1)))

@[irreducible]
def a12437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha12437 : a12437.IsHomogeneous 42 := by
  unfold a12437
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a12438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12437 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a12428 ^ 1)
theorem ha12438 : a12438.IsHomogeneous 42 := by
  unfold a12438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12437.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha12428.pow 1)))

@[irreducible]
def a12439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00130 ^ 1 * a00262 ^ 1)
theorem ha12439 : a12439.IsHomogeneous 48 := by
  unfold a12439
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00130.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12439 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12429 ^ 1) + (C ((28 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a12437 ^ 1)
theorem ha12440 : a12440.IsHomogeneous 48 := by
  unfold a12440
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12439.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12429.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha12437.pow 1)))

@[irreducible]
def a12441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12440 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12430 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12438 ^ 1)
theorem ha12441 : a12441.IsHomogeneous 48 := by
  unfold a12441
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12440.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12430.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12438.pow 1)))

@[irreducible]
def a12442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1)
theorem ha12442 : a12442.IsHomogeneous 48 := by
  unfold a12442
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12439 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a12442 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12434 ^ 1)
theorem ha12443 : a12443.IsHomogeneous 48 := by
  unfold a12443
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12439.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha12442.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12434.pow 1)))

@[irreducible]
def a12444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12443 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12435 ^ 1)
theorem ha12444 : a12444.IsHomogeneous 48 := by
  unfold a12444
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12443.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12435.pow 1)))

@[irreducible]
def a12445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12444 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12436 ^ 1)
theorem ha12445 : a12445.IsHomogeneous 48 := by
  unfold a12445
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12441.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12444.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12436.pow 1)))

@[irreducible]
def a12446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a01716 ^ 1)
theorem ha12446 : a12446.IsHomogeneous 40 := by
  unfold a12446
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a03590 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01716 ^ 1)
theorem ha12447 : a12447.IsHomogeneous 45 := by
  unfold a12447
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha03590.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01716.pow 1)))

@[irreducible]
def a12448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12447 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12427 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a12446 ^ 1)
theorem ha12448 : a12448.IsHomogeneous 46 := by
  unfold a12448
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12447.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12427.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha12446.pow 1)))

@[irreducible]
def a12449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12428 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a12446 ^ 1)
theorem ha12449 : a12449.IsHomogeneous 40 := by
  unfold a12449
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12428.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha12446.pow 1)))

@[irreducible]
def a12450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12448 ^ 1) + (C ((63 : ℂ) / (10 : ℂ)) * a00003 ^ 6 * a12449 ^ 1)
theorem ha12450 : a12450.IsHomogeneous 46 := by
  unfold a12450
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12430.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12448.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((63 : ℂ) / (10 : ℂ))).mul (ha00003.pow 6)).mul (ha12449.pow 1)))

@[irreducible]
def a12451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a06772 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a03590 ^ 1)
theorem ha12451 : a12451.IsHomogeneous 42 := by
  unfold a12451
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha03590.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha06772.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12432 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12447 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a12451 ^ 1)
theorem ha12452 : a12452.IsHomogeneous 45 := by
  unfold a12452
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12432.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12447.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha12451.pow 1)))

@[irreducible]
def a12453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12448 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a12452 ^ 1)
theorem ha12453 : a12453.IsHomogeneous 46 := by
  unfold a12453
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12448.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha12452.pow 1)))

@[irreducible]
def a12454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12450 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12453 ^ 1)
theorem ha12454 : a12454.IsHomogeneous 46 := by
  unfold a12454
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12450.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12453.pow 1)))

@[irreducible]
def a12455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12438 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a12449 ^ 1)
theorem ha12455 : a12455.IsHomogeneous 42 := by
  unfold a12455
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12438.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha12449.pow 1)))

@[irreducible]
def a12456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12441 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12450 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12455 ^ 1)
theorem ha12456 : a12456.IsHomogeneous 48 := by
  unfold a12456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12450.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12455.pow 1)))

@[irreducible]
def a12457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12456 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12454 ^ 1)
theorem ha12457 : a12457.IsHomogeneous 48 := by
  unfold a12457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12456.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12454.pow 1)))

@[irreducible]
def a12458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a03590 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01716 ^ 1)
theorem ha12458 : a12458.IsHomogeneous 45 := by
  unfold a12458
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha03590.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01716.pow 1)))

@[irreducible]
def a12459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00717 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00717 ^ 1)
theorem ha12459 : a12459.IsHomogeneous 46 := by
  unfold a12459
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00717.pow 1)))

@[irreducible]
def a12460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12459 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12446 ^ 1)
theorem ha12460 : a12460.IsHomogeneous 46 := by
  unfold a12460
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12459.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12446.pow 1)))

@[irreducible]
def a12461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a06772 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a03590 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a03590 ^ 1)
theorem ha12461 : a12461.IsHomogeneous 48 := by
  unfold a12461
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a12462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12461 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12447 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a12458 ^ 1)
theorem ha12462 : a12462.IsHomogeneous 48 := by
  unfold a12462
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12447.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha12458.pow 1)))

@[irreducible]
def a12463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12462 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12448 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a12460 ^ 1)
theorem ha12463 : a12463.IsHomogeneous 48 := by
  unfold a12463
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12462.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12448.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha12460.pow 1)))

@[irreducible]
def a12464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00262 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00262 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00717 ^ 1)
theorem ha12464 : a12464.IsHomogeneous 46 := by
  unfold a12464
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a12465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12459 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12464 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00003 ^ 6 * a12428 ^ 1)
theorem ha12465 : a12465.IsHomogeneous 46 := by
  unfold a12465
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12459.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12464.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00003.pow 6)).mul (ha12428.pow 1)))

@[irreducible]
def a12466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12460 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12465 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a12449 ^ 1)
theorem ha12466 : a12466.IsHomogeneous 46 := by
  unfold a12466
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12460.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12465.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha12449.pow 1)))

@[irreducible]
def a12467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12463 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12450 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a12466 ^ 1)
theorem ha12467 : a12467.IsHomogeneous 48 := by
  unfold a12467
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12463.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12450.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha12466.pow 1)))

@[irreducible]
def a12468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a12281 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a06772 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a06772 ^ 1)
theorem ha12468 : a12468.IsHomogeneous 48 := by
  unfold a12468
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha12281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha06772.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha06772.pow 1)))

@[irreducible]
def a12469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12461 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12468 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a12451 ^ 1)
theorem ha12469 : a12469.IsHomogeneous 48 := by
  unfold a12469
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12468.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha12451.pow 1)))

@[irreducible]
def a12470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12462 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12469 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a12452 ^ 1)
theorem ha12470 : a12470.IsHomogeneous 48 := by
  unfold a12470
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12469.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha12452.pow 1)))

@[irreducible]
def a12471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12470 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12453 ^ 1)
theorem ha12471 : a12471.IsHomogeneous 48 := by
  unfold a12471
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12470.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12453.pow 1)))

@[irreducible]
def a12472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12471 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12454 ^ 1)
theorem ha12472 : a12472.IsHomogeneous 48 := by
  unfold a12472
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12471.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12454.pow 1)))

@[irreducible]
def a12473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00103 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00009 ^ 1 * a00262 ^ 1)
theorem ha12473 : a12473.IsHomogeneous 48 := by
  unfold a12473
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a12474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12473 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12437 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12464 ^ 1)
theorem ha12474 : a12474.IsHomogeneous 48 := by
  unfold a12474
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12437.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12464.pow 1)))

@[irreducible]
def a12475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12474 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12465 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12438 ^ 1)
theorem ha12475 : a12475.IsHomogeneous 48 := by
  unfold a12475
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12474.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12465.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12438.pow 1)))

@[irreducible]
def a12476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12475 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a12466 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12455 ^ 1)
theorem ha12476 : a12476.IsHomogeneous 48 := by
  unfold a12476
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12475.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha12466.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12455.pow 1)))

@[irreducible]
def a12477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12456 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12467 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a12476 ^ 1)
theorem ha12477 : a12477.IsHomogeneous 48 := by
  unfold a12477
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12467.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha12476.pow 1)))

@[irreducible]
def a12478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12477 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12472 ^ 1)
theorem ha12478 : a12478.IsHomogeneous 48 := by
  unfold a12478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12457.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12477.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12472.pow 1)))

@[irreducible]
def a12479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00722 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01723 ^ 1)
theorem ha12479 : a12479.IsHomogeneous 50 := by
  unfold a12479
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01723.pow 1)))

@[irreducible]
def a12480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01723 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a03600 ^ 1)
theorem ha12480 : a12480.IsHomogeneous 49 := by
  unfold a12480
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01723.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha03600.pow 1)))

@[irreducible]
def a12481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12479 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12480 ^ 1)
theorem ha12481 : a12481.IsHomogeneous 50 := by
  unfold a12481
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12479.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12480.pow 1)))

@[irreducible]
def a12482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00722 ^ 1)
theorem ha12482 : a12482.IsHomogeneous 50 := by
  unfold a12482
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00722.pow 1)))

@[irreducible]
def a12483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12479 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12482 ^ 1)
theorem ha12483 : a12483.IsHomogeneous 50 := by
  unfold a12483
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12482.pow 1)))

@[irreducible]
def a12484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12483 ^ 1)
theorem ha12484 : a12484.IsHomogeneous 50 := by
  unfold a12484
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12483.pow 1)))

@[irreducible]
def a12485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00104 ^ 1)
theorem ha12485 : a12485.IsHomogeneous 25 := by
  unfold a12485
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00104.pow 1)))

@[irreducible]
def a12486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a12485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12482 ^ 1)
theorem ha12486 : a12486.IsHomogeneous 50 := by
  unfold a12486
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha12485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12482.pow 1)))

@[irreducible]
def a12487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12483 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12486 ^ 1)
theorem ha12487 : a12487.IsHomogeneous 50 := by
  unfold a12487
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12486.pow 1)))

@[irreducible]
def a12488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12487 ^ 1)
theorem ha12488 : a12488.IsHomogeneous 50 := by
  unfold a12488
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12487.pow 1)))

@[irreducible]
def a12489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03600 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 4 * a06785 ^ 1)
theorem ha12489 : a12489.IsHomogeneous 48 := by
  unfold a12489
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03600.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 4)).mul (ha06785.pow 1)))

@[irreducible]
def a12490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12480 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a12489 ^ 1)
theorem ha12490 : a12490.IsHomogeneous 49 := by
  unfold a12490
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12480.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha12489.pow 1)))

@[irreducible]
def a12491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12481 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12490 ^ 1)
theorem ha12491 : a12491.IsHomogeneous 50 := by
  unfold a12491
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12481.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12490.pow 1)))

@[irreducible]
def a12492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12491 ^ 1)
theorem ha12492 : a12492.IsHomogeneous 50 := by
  unfold a12492
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12491.pow 1)))

@[irreducible]
def a12493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12492 ^ 1)
theorem ha12493 : a12493.IsHomogeneous 50 := by
  unfold a12493
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12492.pow 1)))

@[irreducible]
def a12494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a12298 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06785 ^ 1)
theorem ha12494 : a12494.IsHomogeneous 50 := by
  unfold a12494
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha12298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06785.pow 1)))

@[irreducible]
def a12495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12494 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a12489 ^ 1)
theorem ha12495 : a12495.IsHomogeneous 50 := by
  unfold a12495
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12494.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha12489.pow 1)))

@[irreducible]
def a12496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12495 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12490 ^ 1)
theorem ha12496 : a12496.IsHomogeneous 50 := by
  unfold a12496
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12495.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12490.pow 1)))

@[irreducible]
def a12497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12491 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a12496 ^ 1)
theorem ha12497 : a12497.IsHomogeneous 50 := by
  unfold a12497
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha12496.pow 1)))

@[irreducible]
def a12498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12497 ^ 1)
theorem ha12498 : a12498.IsHomogeneous 50 := by
  unfold a12498
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12497.pow 1)))

@[irreducible]
def a12499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12493 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12498 ^ 1)
theorem ha12499 : a12499.IsHomogeneous 50 := by
  unfold a12499
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12498.pow 1)))

@[irreducible]
def a12500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1 * a03597 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01469 ^ 1 * a01721 ^ 1)
theorem ha12500 : a12500.IsHomogeneous 31 := by
  unfold a12500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)).mul (ha03597.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01469.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a12501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a01469 ^ 1 * a01721 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00721 ^ 1 * a03186 ^ 1)
theorem ha12501 : a12501.IsHomogeneous 30 := by
  unfold a12501
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha01469.pow 1)).mul (ha01721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00721.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a12502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12500 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12501 ^ 1)
theorem ha12502 : a12502.IsHomogeneous 31 := by
  unfold a12502
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12500.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12501.pow 1)))

@[irreducible]
def a12503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a06781 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00574 ^ 1 * a03597 ^ 1)
theorem ha12503 : a12503.IsHomogeneous 31 := by
  unfold a12503
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00574.pow 1)).mul (ha03597.pow 1)))

@[irreducible]
def a12504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12500 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a12503 ^ 1)
theorem ha12504 : a12504.IsHomogeneous 31 := by
  unfold a12504
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12500.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha12503.pow 1)))

@[irreducible]
def a12505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12502 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12504 ^ 1)
theorem ha12505 : a12505.IsHomogeneous 31 := by
  unfold a12505
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12502.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12504.pow 1)))

@[irreducible]
def a12506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a06152 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a03186 ^ 1)
theorem ha12506 : a12506.IsHomogeneous 31 := by
  unfold a12506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha06152.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a12507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a12501 ^ 1)
theorem ha12507 : a12507.IsHomogeneous 31 := by
  unfold a12507
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha12501.pow 1)))

@[irreducible]
def a12508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12502 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a12507 ^ 1)
theorem ha12508 : a12508.IsHomogeneous 31 := by
  unfold a12508
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12502.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha12507.pow 1)))

@[irreducible]
def a12509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12505 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12508 ^ 1)
theorem ha12509 : a12509.IsHomogeneous 31 := by
  unfold a12509
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12505.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12508.pow 1)))

@[irreducible]
def a12510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a06781 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a12293 ^ 1)
theorem ha12510 : a12510.IsHomogeneous 25 := by
  unfold a12510
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha12293.pow 1)))

@[irreducible]
def a12511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a12510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12503 ^ 1)
theorem ha12511 : a12511.IsHomogeneous 31 := by
  unfold a12511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha12510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12503.pow 1)))

@[irreducible]
def a12512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12504 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a12511 ^ 1)
theorem ha12512 : a12512.IsHomogeneous 31 := by
  unfold a12512
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha12511.pow 1)))

@[irreducible]
def a12513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12505 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12512 ^ 1)
theorem ha12513 : a12513.IsHomogeneous 31 := by
  unfold a12513
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12505.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12512.pow 1)))

@[irreducible]
def a12514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12509 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12513 ^ 1)
theorem ha12514 : a12514.IsHomogeneous 31 := by
  unfold a12514
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12513.pow 1)))

@[irreducible]
def a12515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a11369 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a06152 ^ 1)
theorem ha12515 : a12515.IsHomogeneous 31 := by
  unfold a12515
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha11369.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha06152.pow 1)))

@[irreducible]
def a12516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12515 ^ 1)
theorem ha12516 : a12516.IsHomogeneous 31 := by
  unfold a12516
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12515.pow 1)))

@[irreducible]
def a12517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12516 ^ 1)
theorem ha12517 : a12517.IsHomogeneous 31 := by
  unfold a12517
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12507.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12516.pow 1)))

@[irreducible]
def a12518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12508 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a12517 ^ 1)
theorem ha12518 : a12518.IsHomogeneous 31 := by
  unfold a12518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha12517.pow 1)))

@[irreducible]
def a12519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12509 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12518 ^ 1)
theorem ha12519 : a12519.IsHomogeneous 31 := by
  unfold a12519
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12518.pow 1)))

@[irreducible]
def a12520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12514 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12519 ^ 1)
theorem ha12520 : a12520.IsHomogeneous 31 := by
  unfold a12520
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12514.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12519.pow 1)))

@[irreducible]
def a12521 : Poly := (C ((-7 : ℂ) / (432 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 2 * a12520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a12499 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a12478 ^ 1)
theorem ha12521 : a12521.IsHomogeneous 55 := by
  unfold a12521
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (432 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha12520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha12499.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha12478.pow 1)))

@[irreducible]
def a12522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a12521 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00276 ^ 1 * a06926 ^ 1)
theorem ha12522 : a12522.IsHomogeneous 86 := by
  unfold a12522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha12521.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00276.pow 1)).mul (ha06926.pow 1)))

@[irreducible]
def a12523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12522 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12420 ^ 1)
theorem ha12523 : a12523.IsHomogeneous 87 := by
  unfold a12523
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12420.pow 1)))

@[irreducible]
def a12524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12421 ^ 1) + (C ((1 : ℂ) / (30 : ℂ)) * a12523 ^ 1)
theorem ha12524 : a12524.IsHomogeneous 87 := by
  unfold a12524
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (30 : ℂ))).mul (ha12523.pow 1)))

@[irreducible]
def a12525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12524 ^ 1)
theorem ha12525 : a12525.IsHomogeneous 87 := by
  unfold a12525
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12524.pow 1)))

@[irreducible]
def a12526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12525 ^ 1)
theorem ha12526 : a12526.IsHomogeneous 87 := by
  unfold a12526
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12525.pow 1)))

@[irreducible]
def a12527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00119 ^ 1 * a07557 ^ 1) + (C ((1 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 2 * a10779 ^ 1) + (C ((7 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1)
theorem ha12527 : a12527.IsHomogeneous 25 := by
  unfold a12527
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00119.pow 1)).mul (ha07557.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 2)).mul (ha10779.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a12528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1 * a12527 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00275 ^ 1 * a06931 ^ 1)
theorem ha12528 : a12528.IsHomogeneous 86 := by
  unfold a12528
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).mul (ha12527.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00275.pow 1)).mul (ha06931.pow 1)))

@[irreducible]
def a12529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12423 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a12528 ^ 1)
theorem ha12529 : a12529.IsHomogeneous 86 := by
  unfold a12529
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha12528.pow 1)))

@[irreducible]
def a12530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a12529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12424 ^ 1)
theorem ha12530 : a12530.IsHomogeneous 87 := by
  unfold a12530
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha12529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12424.pow 1)))

@[irreducible]
def a12531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12425 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12530 ^ 1)
theorem ha12531 : a12531.IsHomogeneous 87 := by
  unfold a12531
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12530.pow 1)))

@[irreducible]
def a12532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12531 ^ 1)
theorem ha12532 : a12532.IsHomogeneous 87 := by
  unfold a12532
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12531.pow 1)))

@[irreducible]
def a12533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12532 ^ 1)
theorem ha12533 : a12533.IsHomogeneous 87 := by
  unfold a12533
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12526.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12532.pow 1)))

@[irreducible]
def a12534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00280 ^ 1 * a00717 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00717 ^ 1 * a00762 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00280 ^ 1 * a01716 ^ 1)
theorem ha12534 : a12534.IsHomogeneous 86 := by
  unfold a12534
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00280.pow 1)).mul (ha00717.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00717.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a00762 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1 * a00762 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a01801 ^ 1)
theorem ha12535 : a12535.IsHomogeneous 86 := by
  unfold a12535
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha00762.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a12536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a00280 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00280 ^ 1 * a00717 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00262 ^ 1 * a00762 ^ 1)
theorem ha12536 : a12536.IsHomogeneous 86 := by
  unfold a12536
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha00280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00280.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a12537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12534 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12535 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a12536 ^ 1)
theorem ha12537 : a12537.IsHomogeneous 86 := by
  unfold a12537
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12535.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha12536.pow 1)))

@[irreducible]
def a12538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00717 ^ 1 * a00762 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a01801 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00762 ^ 1 * a01716 ^ 1)
theorem ha12538 : a12538.IsHomogeneous 91 := by
  unfold a12538
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00717.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha01801.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00762.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00280 ^ 1 * a03590 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00130 ^ 1 * a00762 ^ 1 * a01716 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00280 ^ 1 * a01716 ^ 1)
theorem ha12539 : a12539.IsHomogeneous 91 := by
  unfold a12539
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha03590.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00130.pow 1)).mul (ha00762.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00280.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a12540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12534 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12538 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a12539 ^ 1)
theorem ha12540 : a12540.IsHomogeneous 91 := by
  unfold a12540
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12538.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha12539.pow 1)))

@[irreducible]
def a12541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00262 ^ 1 * a03728 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a01801 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00262 ^ 1 * a01801 ^ 1)
theorem ha12541 : a12541.IsHomogeneous 91 := by
  unfold a12541
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha03728.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha01801.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a12542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12538 ^ 1) + (C ((12 : ℂ) / (35 : ℂ)) * a12541 ^ 1)
theorem ha12542 : a12542.IsHomogeneous 91 := by
  unfold a12542
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12538.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (35 : ℂ))).mul (ha12541.pow 1)))

@[irreducible]
def a12543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a12537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12540 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12542 ^ 1)
theorem ha12543 : a12543.IsHomogeneous 91 := by
  unfold a12543
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha12537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12540.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12542.pow 1)))

end CycleQ2Concrete
