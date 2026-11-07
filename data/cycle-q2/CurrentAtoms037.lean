import Proposal.CurrentAtoms036

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a11264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha11264 : a11264.IsHomogeneous 12 := by
  unfold a11264
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a11265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11259 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11264 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11263 ^ 1)
theorem ha11265 : a11265.IsHomogeneous 18 := by
  unfold a11265
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11259.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11264.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11263.pow 1)))

@[irreducible]
def a11266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11260 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a11263 ^ 1)
theorem ha11266 : a11266.IsHomogeneous 12 := by
  unfold a11266
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha11263.pow 1)))

@[irreducible]
def a11267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11265 ^ 1) + (C ((21 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11266 ^ 1)
theorem ha11267 : a11267.IsHomogeneous 18 := by
  unfold a11267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11265.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11266.pow 1)))

@[irreducible]
def a11268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha11268 : a11268.IsHomogeneous 18 := by
  unfold a11268
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01327 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a02935 ^ 1)
theorem ha11269 : a11269.IsHomogeneous 12 := by
  unfold a11269
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11259 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11268 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a11269 ^ 1)
theorem ha11270 : a11270.IsHomogeneous 18 := by
  unfold a11270
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11268.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha11269.pow 1)))

@[irreducible]
def a11271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1)
theorem ha11271 : a11271.IsHomogeneous 18 := by
  unfold a11271
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11268 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11271 ^ 1)
theorem ha11272 : a11272.IsHomogeneous 18 := by
  unfold a11272
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11261.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11268.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11271.pow 1)))

@[irreducible]
def a11273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11270 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11272 ^ 1)
theorem ha11273 : a11273.IsHomogeneous 18 := by
  unfold a11273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11270.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11272.pow 1)))

@[irreducible]
def a11274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02935 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a05754 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a02935 ^ 1)
theorem ha11274 : a11274.IsHomogeneous 12 := by
  unfold a11274
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha05754.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11264 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11269 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a11274 ^ 1)
theorem ha11275 : a11275.IsHomogeneous 12 := by
  unfold a11275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11269.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha11274.pow 1)))

@[irreducible]
def a11276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11265 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11270 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11275 ^ 1)
theorem ha11276 : a11276.IsHomogeneous 18 := by
  unfold a11276
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11270.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11275.pow 1)))

@[irreducible]
def a11277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11276 ^ 1)
theorem ha11277 : a11277.IsHomogeneous 18 := by
  unfold a11277
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11273.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11276.pow 1)))

@[irreducible]
def a11278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha11278 : a11278.IsHomogeneous 6 := by
  unfold a11278
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a11279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11260 ^ 1)
theorem ha11279 : a11279.IsHomogeneous 12 := by
  unfold a11279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11260.pow 1)))

@[irreducible]
def a11280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha11280 : a11280.IsHomogeneous 12 := by
  unfold a11280
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a11281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11261 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11278 ^ 1)
theorem ha11281 : a11281.IsHomogeneous 18 := by
  unfold a11281
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11261.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11278.pow 1)))

@[irreducible]
def a11282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11262 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11281 ^ 1) + (C ((21 : ℂ) / (16 : ℂ)) * a00003 ^ 6 * a11279 ^ 1)
theorem ha11282 : a11282.IsHomogeneous 18 := by
  unfold a11282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11281.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (16 : ℂ))).mul (ha00003.pow 6)).mul (ha11279.pow 1)))

@[irreducible]
def a11283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11279 ^ 1)
theorem ha11283 : a11283.IsHomogeneous 12 := by
  unfold a11283
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11279.pow 1)))

@[irreducible]
def a11284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11282 ^ 1) + (C ((21 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11283 ^ 1)
theorem ha11284 : a11284.IsHomogeneous 18 := by
  unfold a11284
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11282.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11283.pow 1)))

@[irreducible]
def a11285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha11285 : a11285.IsHomogeneous 12 := by
  unfold a11285
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a11286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11280 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11285 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11271 ^ 1)
theorem ha11286 : a11286.IsHomogeneous 18 := by
  unfold a11286
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11285.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11271.pow 1)))

@[irreducible]
def a11287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11286 ^ 1)
theorem ha11287 : a11287.IsHomogeneous 18 := by
  unfold a11287
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11281.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11286.pow 1)))

@[irreducible]
def a11288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11282 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11287 ^ 1)
theorem ha11288 : a11288.IsHomogeneous 18 := by
  unfold a11288
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11282.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11287.pow 1)))

@[irreducible]
def a11289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11277 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11288 ^ 1)
theorem ha11289 : a11289.IsHomogeneous 18 := by
  unfold a11289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11284.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11288.pow 1)))

@[irreducible]
def a11290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a01327 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00506 ^ 1)
theorem ha11290 : a11290.IsHomogeneous 18 := by
  unfold a11290
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00506.pow 1)))

@[irreducible]
def a11291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha11291 : a11291.IsHomogeneous 12 := by
  unfold a11291
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02935.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a11292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11290 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11291 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11263 ^ 1)
theorem ha11292 : a11292.IsHomogeneous 18 := by
  unfold a11292
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11290.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11291.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11263.pow 1)))

@[irreducible]
def a11293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a02935 ^ 1)
theorem ha11293 : a11293.IsHomogeneous 18 := by
  unfold a11293
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11293 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11264 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11291 ^ 1)
theorem ha11294 : a11294.IsHomogeneous 18 := by
  unfold a11294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11264.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11291.pow 1)))

@[irreducible]
def a11295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11265 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11294 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11292 ^ 1)
theorem ha11295 : a11295.IsHomogeneous 18 := by
  unfold a11295
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11294.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11292.pow 1)))

@[irreducible]
def a11296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1)
theorem ha11296 : a11296.IsHomogeneous 18 := by
  unfold a11296
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11290 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11296 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11260 ^ 1)
theorem ha11297 : a11297.IsHomogeneous 18 := by
  unfold a11297
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11296.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11260.pow 1)))

@[irreducible]
def a11298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11297 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11266 ^ 1)
theorem ha11298 : a11298.IsHomogeneous 18 := by
  unfold a11298
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11297.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11266.pow 1)))

@[irreducible]
def a11299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11295 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11298 ^ 1)
theorem ha11299 : a11299.IsHomogeneous 18 := by
  unfold a11299
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11295.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11298.pow 1)))

@[irreducible]
def a11300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a10779 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a05754 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a05754 ^ 1)
theorem ha11300 : a11300.IsHomogeneous 18 := by
  unfold a11300
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha10779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha05754.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a11301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11293 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11300 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11274 ^ 1)
theorem ha11301 : a11301.IsHomogeneous 18 := by
  unfold a11301
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11293.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11300.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11274.pow 1)))

@[irreducible]
def a11302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11301 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11275 ^ 1)
theorem ha11302 : a11302.IsHomogeneous 18 := by
  unfold a11302
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11294.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11301.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11275.pow 1)))

@[irreducible]
def a11303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11276 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11295 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11302 ^ 1)
theorem ha11303 : a11303.IsHomogeneous 18 := by
  unfold a11303
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11276.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11295.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11302.pow 1)))

@[irreducible]
def a11304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11277 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11303 ^ 1)
theorem ha11304 : a11304.IsHomogeneous 18 := by
  unfold a11304
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11299.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11303.pow 1)))

@[irreducible]
def a11305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha11305 : a11305.IsHomogeneous 12 := by
  unfold a11305
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a11306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11305 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11296 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11278 ^ 1)
theorem ha11306 : a11306.IsHomogeneous 18 := by
  unfold a11306
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11305.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11296.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11278.pow 1)))

@[irreducible]
def a11307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11297 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11306 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a11279 ^ 1)
theorem ha11307 : a11307.IsHomogeneous 18 := by
  unfold a11307
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11297.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11306.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha11279.pow 1)))

@[irreducible]
def a11308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11307 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11283 ^ 1)
theorem ha11308 : a11308.IsHomogeneous 18 := by
  unfold a11308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11307.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11283.pow 1)))

@[irreducible]
def a11309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11299 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11308 ^ 1)
theorem ha11309 : a11309.IsHomogeneous 18 := by
  unfold a11309
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11284.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11299.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11308.pow 1)))

@[irreducible]
def a11310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11289 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11309 ^ 1)
theorem ha11310 : a11310.IsHomogeneous 18 := by
  unfold a11310
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11289.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11304.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11309.pow 1)))

@[irreducible]
def a11311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00570 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a01461 ^ 1)
theorem ha11311 : a11311.IsHomogeneous 18 := by
  unfold a11311
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha01461.pow 1)))

@[irreducible]
def a11312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01461 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03172 ^ 1)
theorem ha11312 : a11312.IsHomogeneous 18 := by
  unfold a11312
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03172.pow 1)))

@[irreducible]
def a11313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11311 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11312 ^ 1)
theorem ha11313 : a11313.IsHomogeneous 18 := by
  unfold a11313
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11311.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11312.pow 1)))

@[irreducible]
def a11314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00176 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00570 ^ 1)
theorem ha11314 : a11314.IsHomogeneous 18 := by
  unfold a11314
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00570.pow 1)))

@[irreducible]
def a11315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11311 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11314 ^ 1)
theorem ha11315 : a11315.IsHomogeneous 18 := by
  unfold a11315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11311.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11314.pow 1)))

@[irreducible]
def a11316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11313 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11315 ^ 1)
theorem ha11316 : a11316.IsHomogeneous 18 := by
  unfold a11316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11313.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11315.pow 1)))

@[irreducible]
def a11317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha11317 : a11317.IsHomogeneous 12 := by
  unfold a11317
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a11318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11314 ^ 1)
theorem ha11318 : a11318.IsHomogeneous 18 := by
  unfold a11318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11314.pow 1)))

@[irreducible]
def a11319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11315 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11318 ^ 1)
theorem ha11319 : a11319.IsHomogeneous 18 := by
  unfold a11319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11315.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11318.pow 1)))

@[irreducible]
def a11320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11319 ^ 1)
theorem ha11320 : a11320.IsHomogeneous 18 := by
  unfold a11320
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11319.pow 1)))

@[irreducible]
def a11321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03172 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a06131 ^ 1)
theorem ha11321 : a11321.IsHomogeneous 12 := by
  unfold a11321
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha06131.pow 1)))

@[irreducible]
def a11322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11312 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11321 ^ 1)
theorem ha11322 : a11322.IsHomogeneous 18 := by
  unfold a11322
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11312.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11321.pow 1)))

@[irreducible]
def a11323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11313 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11322 ^ 1)
theorem ha11323 : a11323.IsHomogeneous 18 := by
  unfold a11323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11313.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11322.pow 1)))

@[irreducible]
def a11324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11323 ^ 1)
theorem ha11324 : a11324.IsHomogeneous 18 := by
  unfold a11324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11323.pow 1)))

@[irreducible]
def a11325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11320 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11324 ^ 1)
theorem ha11325 : a11325.IsHomogeneous 18 := by
  unfold a11325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11320.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11324.pow 1)))

@[irreducible]
def a11326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a02949 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01335 ^ 1)
theorem ha11326 : a11326.IsHomogeneous 12 := by
  unfold a11326
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01335.pow 1)))

@[irreducible]
def a11327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11326 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03108 ^ 1)
theorem ha11327 : a11327.IsHomogeneous 12 := by
  unfold a11327
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11326.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03108.pow 1)))

@[irreducible]
def a11328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a05775 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a02949 ^ 1)
theorem ha11328 : a11328.IsHomogeneous 12 := by
  unfold a11328
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a11329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11326 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11328 ^ 1)
theorem ha11329 : a11329.IsHomogeneous 12 := by
  unfold a11329
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11328.pow 1)))

@[irreducible]
def a11330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11329 ^ 1)
theorem ha11330 : a11330.IsHomogeneous 12 := by
  unfold a11330
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11329.pow 1)))

@[irreducible]
def a11331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a10809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a05775 ^ 1)
theorem ha11331 : a11331.IsHomogeneous 12 := by
  unfold a11331
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha10809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha05775.pow 1)))

@[irreducible]
def a11332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11331 ^ 1)
theorem ha11332 : a11332.IsHomogeneous 12 := by
  unfold a11332
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11331.pow 1)))

@[irreducible]
def a11333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11329 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11332 ^ 1)
theorem ha11333 : a11333.IsHomogeneous 12 := by
  unfold a11333
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11332.pow 1)))

@[irreducible]
def a11334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11333 ^ 1)
theorem ha11334 : a11334.IsHomogeneous 12 := by
  unfold a11334
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11333.pow 1)))

@[irreducible]
def a11335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03109 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a11327 ^ 1)
theorem ha11335 : a11335.IsHomogeneous 12 := by
  unfold a11335
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha11327.pow 1)))

@[irreducible]
def a11336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11330 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11335 ^ 1)
theorem ha11336 : a11336.IsHomogeneous 12 := by
  unfold a11336
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11335.pow 1)))

@[irreducible]
def a11337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11336 ^ 1)
theorem ha11337 : a11337.IsHomogeneous 12 := by
  unfold a11337
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11336.pow 1)))

@[irreducible]
def a11338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11335 ^ 1)
theorem ha11338 : a11338.IsHomogeneous 12 := by
  unfold a11338
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11335.pow 1)))

@[irreducible]
def a11339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11336 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11338 ^ 1)
theorem ha11339 : a11339.IsHomogeneous 12 := by
  unfold a11339
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11336.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11338.pow 1)))

@[irreducible]
def a11340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11339 ^ 1)
theorem ha11340 : a11340.IsHomogeneous 12 := by
  unfold a11340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11339.pow 1)))

@[irreducible]
def a11341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a11340 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06131 ^ 1)
theorem ha11341 : a11341.IsHomogeneous 18 := by
  unfold a11341
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha11340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06131.pow 1)))

@[irreducible]
def a11342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11341 ^ 1) + (C ((5 : ℂ) / (14 : ℂ)) * a00003 ^ 6 * a11321 ^ 1)
theorem ha11342 : a11342.IsHomogeneous 18 := by
  unfold a11342
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11341.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (14 : ℂ))).mul (ha00003.pow 6)).mul (ha11321.pow 1)))

@[irreducible]
def a11343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11322 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a11342 ^ 1)
theorem ha11343 : a11343.IsHomogeneous 18 := by
  unfold a11343
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11322.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha11342.pow 1)))

@[irreducible]
def a11344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11323 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11343 ^ 1)
theorem ha11344 : a11344.IsHomogeneous 18 := by
  unfold a11344
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11343.pow 1)))

@[irreducible]
def a11345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11344 ^ 1)
theorem ha11345 : a11345.IsHomogeneous 18 := by
  unfold a11345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11344.pow 1)))

@[irreducible]
def a11346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11325 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11345 ^ 1)
theorem ha11346 : a11346.IsHomogeneous 18 := by
  unfold a11346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11345.pow 1)))

@[irreducible]
def a11347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1 * a02949 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01335 ^ 1 * a01469 ^ 1)
theorem ha11347 : a11347.IsHomogeneous 18 := by
  unfold a11347
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)).mul (ha02949.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01335.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a11348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1 * a03186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01335 ^ 1 * a01469 ^ 1)
theorem ha11348 : a11348.IsHomogeneous 12 := by
  unfold a11348
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01335.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a11349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11347 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11348 ^ 1)
theorem ha11349 : a11349.IsHomogeneous 18 := by
  unfold a11349
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11347.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11348.pow 1)))

@[irreducible]
def a11350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a05775 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00574 ^ 1 * a02949 ^ 1)
theorem ha11350 : a11350.IsHomogeneous 18 := by
  unfold a11350
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00574.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a11351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11347 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a11350 ^ 1)
theorem ha11351 : a11351.IsHomogeneous 18 := by
  unfold a11351
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha11350.pow 1)))

@[irreducible]
def a11352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11349 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11351 ^ 1)
theorem ha11352 : a11352.IsHomogeneous 18 := by
  unfold a11352
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11349.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11351.pow 1)))

@[irreducible]
def a11353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a05775 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a10809 ^ 1)
theorem ha11353 : a11353.IsHomogeneous 12 := by
  unfold a11353
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha10809.pow 1)))

@[irreducible]
def a11354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a11353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11350 ^ 1)
theorem ha11354 : a11354.IsHomogeneous 18 := by
  unfold a11354
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha11353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11350.pow 1)))

@[irreducible]
def a11355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11351 ^ 1) + (C ((3 : ℂ) / (7 : ℂ)) * a11354 ^ 1)
theorem ha11355 : a11355.IsHomogeneous 18 := by
  unfold a11355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11351.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (7 : ℂ))).mul (ha11354.pow 1)))

@[irreducible]
def a11356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11355 ^ 1)
theorem ha11356 : a11356.IsHomogeneous 18 := by
  unfold a11356
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11355.pow 1)))

@[irreducible]
def a11357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a06152 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a03186 ^ 1)
theorem ha11357 : a11357.IsHomogeneous 18 := by
  unfold a11357
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha06152.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a11358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11357 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a11348 ^ 1)
theorem ha11358 : a11358.IsHomogeneous 18 := by
  unfold a11358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11357.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha11348.pow 1)))

@[irreducible]
def a11359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11349 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11358 ^ 1)
theorem ha11359 : a11359.IsHomogeneous 18 := by
  unfold a11359
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11349.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11358.pow 1)))

@[irreducible]
def a11360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11359 ^ 1)
theorem ha11360 : a11360.IsHomogeneous 18 := by
  unfold a11360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11359.pow 1)))

@[irreducible]
def a11361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11356 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11360 ^ 1)
theorem ha11361 : a11361.IsHomogeneous 18 := by
  unfold a11361
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11356.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11360.pow 1)))

@[irreducible]
def a11362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6)
theorem ha11362 : a11362.IsHomogeneous 6 := by
  unfold a11362
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11362 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6)
theorem ha11363 : a11363.IsHomogeneous 6 := by
  unfold a11363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11362.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11363 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha11364 : a11364.IsHomogeneous 6 := by
  unfold a11364
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a11365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1)
theorem ha11365 : a11365.IsHomogeneous 6 := by
  unfold a11365
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)))

@[irreducible]
def a11366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11362 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11365 ^ 1)
theorem ha11366 : a11366.IsHomogeneous 6 := by
  unfold a11366
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11362.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11365.pow 1)))

@[irreducible]
def a11367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11366 ^ 1)
theorem ha11367 : a11367.IsHomogeneous 6 := by
  unfold a11367
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11366.pow 1)))

@[irreducible]
def a11368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11364 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11367 ^ 1)
theorem ha11368 : a11368.IsHomogeneous 6 := by
  unfold a11368
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11367.pow 1)))

@[irreducible]
def a11369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11364 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11368 ^ 1)
theorem ha11369 : a11369.IsHomogeneous 6 := by
  unfold a11369
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11368.pow 1)))

@[irreducible]
def a11370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a06152 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11369 ^ 1)
theorem ha11370 : a11370.IsHomogeneous 12 := by
  unfold a11370
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha06152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11369.pow 1)))

@[irreducible]
def a11371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11357 ^ 1)
theorem ha11371 : a11371.IsHomogeneous 18 := by
  unfold a11371
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11370.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11357.pow 1)))

@[irreducible]
def a11372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11358 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11371 ^ 1)
theorem ha11372 : a11372.IsHomogeneous 18 := by
  unfold a11372
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11371.pow 1)))

@[irreducible]
def a11373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11359 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11372 ^ 1)
theorem ha11373 : a11373.IsHomogeneous 18 := by
  unfold a11373
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11372.pow 1)))

@[irreducible]
def a11374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11373 ^ 1)
theorem ha11374 : a11374.IsHomogeneous 18 := by
  unfold a11374
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11360.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11373.pow 1)))

@[irreducible]
def a11375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11361 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11374 ^ 1)
theorem ha11375 : a11375.IsHomogeneous 18 := by
  unfold a11375
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11374.pow 1)))

@[irreducible]
def a11376 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a11346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11310 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a11375 ^ 1)
theorem ha11376 : a11376.IsHomogeneous 18 := by
  unfold a11376
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha11346.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11310.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha11375.pow 1)))

@[irreducible]
def a11377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a06158 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11376 ^ 1)
theorem ha11377 : a11377.IsHomogeneous 24 := by
  unfold a11377
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha06158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11376.pow 1)))

@[irreducible]
def a11378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11377 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11250 ^ 1)
theorem ha11378 : a11378.IsHomogeneous 30 := by
  unfold a11378
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11250.pow 1)))

@[irreducible]
def a11379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11251 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11378 ^ 1)
theorem ha11379 : a11379.IsHomogeneous 30 := by
  unfold a11379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11378.pow 1)))

@[irreducible]
def a11380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11252 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11379 ^ 1)
theorem ha11380 : a11380.IsHomogeneous 30 := by
  unfold a11380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11379.pow 1)))

@[irreducible]
def a11381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11380 ^ 1)
theorem ha11381 : a11381.IsHomogeneous 30 := by
  unfold a11381
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11380.pow 1)))

@[irreducible]
def a11382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11381 ^ 1)
theorem ha11382 : a11382.IsHomogeneous 30 := by
  unfold a11382
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11381.pow 1)))

@[irreducible]
def a11383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a11243 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a11382 ^ 1)
theorem ha11383 : a11383.IsHomogeneous 49 := by
  unfold a11383
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha11243.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha11382.pow 1)))

@[irreducible]
def a11384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01340 ^ 1) + (C ((5 : ℂ) / (16 : ℂ)) * a00317 ^ 1 * a02956 ^ 1)
theorem ha11384 : a11384.IsHomogeneous 45 := by
  unfold a11384
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (16 : ℂ))).mul (ha00317.pow 1)).mul (ha02956.pow 1)))

@[irreducible]
def a11385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00513 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00865 ^ 1 * a01340 ^ 1)
theorem ha11385 : a11385.IsHomogeneous 42 := by
  unfold a11385
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00513.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00865.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a11386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11385 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a11384 ^ 1)
theorem ha11386 : a11386.IsHomogeneous 48 := by
  unfold a11386
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11385.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha11384.pow 1)))

@[irreducible]
def a11387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a05784 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a02956 ^ 1)
theorem ha11387 : a11387.IsHomogeneous 45 := by
  unfold a11387
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha05784.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha02956.pow 1)))

@[irreducible]
def a11388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11384 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a11387 ^ 1)
theorem ha11388 : a11388.IsHomogeneous 45 := by
  unfold a11388
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha11387.pow 1)))

@[irreducible]
def a11389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11386 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a11388 ^ 1)
theorem ha11389 : a11389.IsHomogeneous 48 := by
  unfold a11389
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11386.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha11388.pow 1)))

@[irreducible]
def a11390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a04086 ^ 1)
theorem ha11390 : a11390.IsHomogeneous 36 := by
  unfold a11390
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a11391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11385 ^ 1)
theorem ha11391 : a11391.IsHomogeneous 42 := by
  unfold a11391
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11385.pow 1)))

@[irreducible]
def a11392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11391 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11386 ^ 1)
theorem ha11392 : a11392.IsHomogeneous 48 := by
  unfold a11392
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11391.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11386.pow 1)))

@[irreducible]
def a11393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11392 ^ 1)
theorem ha11393 : a11393.IsHomogeneous 48 := by
  unfold a11393
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11392.pow 1)))

@[irreducible]
def a11394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a10820 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a05784 ^ 1)
theorem ha11394 : a11394.IsHomogeneous 48 := by
  unfold a11394
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha10820.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha05784.pow 1)))

@[irreducible]
def a11395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11394 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11387 ^ 1)
theorem ha11395 : a11395.IsHomogeneous 48 := by
  unfold a11395
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11394.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11387.pow 1)))

@[irreducible]
def a11396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11395 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a11388 ^ 1)
theorem ha11396 : a11396.IsHomogeneous 48 := by
  unfold a11396
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11395.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha11388.pow 1)))

@[irreducible]
def a11397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11389 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a11396 ^ 1)
theorem ha11397 : a11397.IsHomogeneous 48 := by
  unfold a11397
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha11396.pow 1)))

@[irreducible]
def a11398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11397 ^ 1)
theorem ha11398 : a11398.IsHomogeneous 48 := by
  unfold a11398
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11393.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11397.pow 1)))

@[irreducible]
def a11399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a07558 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00157 ^ 1 * a04086 ^ 1)
theorem ha11399 : a11399.IsHomogeneous 30 := by
  unfold a11399
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00157.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a11400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11390 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a11399 ^ 1)
theorem ha11400 : a11400.IsHomogeneous 36 := by
  unfold a11400
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11390.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha11399.pow 1)))

@[irreducible]
def a11401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11391 ^ 1)
theorem ha11401 : a11401.IsHomogeneous 42 := by
  unfold a11401
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11400.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11391.pow 1)))

@[irreducible]
def a11402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11401 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11392 ^ 1)
theorem ha11402 : a11402.IsHomogeneous 48 := by
  unfold a11402
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11392.pow 1)))

@[irreducible]
def a11403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11402 ^ 1)
theorem ha11403 : a11403.IsHomogeneous 48 := by
  unfold a11403
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11393.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11402.pow 1)))

@[irreducible]
def a11404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11398 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11403 ^ 1)
theorem ha11404 : a11404.IsHomogeneous 48 := by
  unfold a11404
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11398.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11403.pow 1)))

@[irreducible]
def a11405 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a11243 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a11404 ^ 1)
theorem ha11405 : a11405.IsHomogeneous 55 := by
  unfold a11405
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha11243.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha11404.pow 1)))

@[irreducible]
def a11406 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a11383 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11405 ^ 1)
theorem ha11406 : a11406.IsHomogeneous 55 := by
  unfold a11406
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha11383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11405.pow 1)))

@[irreducible]
def a11407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00547 ^ 1)
theorem ha11407 : a11407.IsHomogeneous 30 := by
  unfold a11407
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00547 ^ 1)
theorem ha11408 : a11408.IsHomogeneous 30 := by
  unfold a11408
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a01327 ^ 1)
theorem ha11409 : a11409.IsHomogeneous 30 := by
  unfold a11409
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11407 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11409 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11408 ^ 1)
theorem ha11410 : a11410.IsHomogeneous 30 := by
  unfold a11410
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11407.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11409.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11408.pow 1)))

@[irreducible]
def a11411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00547 ^ 1)
theorem ha11411 : a11411.IsHomogeneous 30 := by
  unfold a11411
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a11412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00506 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00168 ^ 1)
theorem ha11412 : a11412.IsHomogeneous 24 := by
  unfold a11412
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a11413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11411 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11407 ^ 1)
theorem ha11413 : a11413.IsHomogeneous 30 := by
  unfold a11413
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11411.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11407.pow 1)))

@[irreducible]
def a11414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a01412 ^ 1)
theorem ha11414 : a11414.IsHomogeneous 30 := by
  unfold a11414
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01412.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11408 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11414 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a11411 ^ 1)
theorem ha11415 : a11415.IsHomogeneous 30 := by
  unfold a11415
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11408.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11414.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha11411.pow 1)))

@[irreducible]
def a11416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11410 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11413 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11415 ^ 1)
theorem ha11416 : a11416.IsHomogeneous 30 := by
  unfold a11416
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11410.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11413.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11415.pow 1)))

@[irreducible]
def a11417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a01327 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00506 ^ 1)
theorem ha11417 : a11417.IsHomogeneous 24 := by
  unfold a11417
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a02935 ^ 1)
theorem ha11418 : a11418.IsHomogeneous 18 := by
  unfold a11418
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11407 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11418 ^ 1)
theorem ha11419 : a11419.IsHomogeneous 30 := by
  unfold a11419
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11407.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11418.pow 1)))

@[irreducible]
def a11420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a02935 ^ 1)
theorem ha11420 : a11420.IsHomogeneous 24 := by
  unfold a11420
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11409 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11418 ^ 1)
theorem ha11421 : a11421.IsHomogeneous 30 := by
  unfold a11421
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11409.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11418.pow 1)))

@[irreducible]
def a11422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11410 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11419 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11421 ^ 1)
theorem ha11422 : a11422.IsHomogeneous 30 := by
  unfold a11422
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11410.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11419.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11421.pow 1)))

@[irreducible]
def a11423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00155 ^ 1 * a00168 ^ 1)
theorem ha11423 : a11423.IsHomogeneous 18 := by
  unfold a11423
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a11424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11412 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11417 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11423 ^ 1)
theorem ha11424 : a11424.IsHomogeneous 24 := by
  unfold a11424
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11417.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11423.pow 1)))

@[irreducible]
def a11425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11413 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11419 ^ 1)
theorem ha11425 : a11425.IsHomogeneous 30 := by
  unfold a11425
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11413.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11419.pow 1)))

@[irreducible]
def a11426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11416 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11422 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11425 ^ 1)
theorem ha11426 : a11426.IsHomogeneous 30 := by
  unfold a11426
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11416.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11422.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11425.pow 1)))

@[irreducible]
def a11427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1)
theorem ha11427 : a11427.IsHomogeneous 24 := by
  unfold a11427
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01412 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03085 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01412 ^ 1)
theorem ha11428 : a11428.IsHomogeneous 18 := by
  unfold a11428
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03085.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11428 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11427 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11411 ^ 1)
theorem ha11429 : a11429.IsHomogeneous 30 := by
  unfold a11429
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11428.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11427.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11411.pow 1)))

@[irreducible]
def a11430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00547 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00168 ^ 1)
theorem ha11430 : a11430.IsHomogeneous 18 := by
  unfold a11430
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a11431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11427 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11430 ^ 1)
theorem ha11431 : a11431.IsHomogeneous 24 := by
  unfold a11431
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11427.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11430.pow 1)))

@[irreducible]
def a11432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11429 ^ 1)
theorem ha11432 : a11432.IsHomogeneous 30 := by
  unfold a11432
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11413.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11429.pow 1)))

@[irreducible]
def a11433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a03085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05994 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03085 ^ 1)
theorem ha11433 : a11433.IsHomogeneous 24 := by
  unfold a11433
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11414 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11428 ^ 1)
theorem ha11434 : a11434.IsHomogeneous 30 := by
  unfold a11434
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11414.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11428.pow 1)))

@[irreducible]
def a11435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11415 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11434 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a11429 ^ 1)
theorem ha11435 : a11435.IsHomogeneous 30 := by
  unfold a11435
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11434.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha11429.pow 1)))

@[irreducible]
def a11436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11416 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11432 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11435 ^ 1)
theorem ha11436 : a11436.IsHomogeneous 30 := by
  unfold a11436
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11416.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11432.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11435.pow 1)))

@[irreducible]
def a11437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1)
theorem ha11437 : a11437.IsHomogeneous 12 := by
  unfold a11437
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00155.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)))

@[irreducible]
def a11438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11423 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a11437 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a11430 ^ 1)
theorem ha11438 : a11438.IsHomogeneous 18 := by
  unfold a11438
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11423.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha11437.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha11430.pow 1)))

@[irreducible]
def a11439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11431 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11438 ^ 1)
theorem ha11439 : a11439.IsHomogeneous 24 := by
  unfold a11439
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11431.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11438.pow 1)))

@[irreducible]
def a11440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11439 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11425 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11432 ^ 1)
theorem ha11440 : a11440.IsHomogeneous 30 := by
  unfold a11440
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11439.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11425.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11432.pow 1)))

@[irreducible]
def a11441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11436 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11440 ^ 1)
theorem ha11441 : a11441.IsHomogeneous 30 := by
  unfold a11441
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11436.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11440.pow 1)))

@[irreducible]
def a11442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00547 ^ 1 * a01327 ^ 1)
theorem ha11442 : a11442.IsHomogeneous 30 := by
  unfold a11442
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a03085 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1 * a01412 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a01412 ^ 1)
theorem ha11443 : a11443.IsHomogeneous 30 := by
  unfold a11443
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha03085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a11444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11408 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11443 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a11442 ^ 1)
theorem ha11444 : a11444.IsHomogeneous 30 := by
  unfold a11444
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11408.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11443.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha11442.pow 1)))

@[irreducible]
def a11445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a02935 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a02935 ^ 1)
theorem ha11445 : a11445.IsHomogeneous 30 := by
  unfold a11445
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11409 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11442 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11445 ^ 1)
theorem ha11446 : a11446.IsHomogeneous 30 := by
  unfold a11446
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11442.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11445.pow 1)))

@[irreducible]
def a11447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11410 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11446 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11444 ^ 1)
theorem ha11447 : a11447.IsHomogeneous 30 := by
  unfold a11447
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11410.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11446.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11444.pow 1)))

@[irreducible]
def a11448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a05994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a03085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a03085 ^ 1)
theorem ha11448 : a11448.IsHomogeneous 30 := by
  unfold a11448
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha05994.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a11449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11443 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11448 ^ 1)
theorem ha11449 : a11449.IsHomogeneous 30 := by
  unfold a11449
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11414.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11443.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11448.pow 1)))

@[irreducible]
def a11450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11415 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11444 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11449 ^ 1)
theorem ha11450 : a11450.IsHomogeneous 30 := by
  unfold a11450
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11444.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11449.pow 1)))

@[irreducible]
def a11451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11416 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11447 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11450 ^ 1)
theorem ha11451 : a11451.IsHomogeneous 30 := by
  unfold a11451
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11416.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11447.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11450.pow 1)))

@[irreducible]
def a11452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a10779 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a05754 ^ 1)
theorem ha11452 : a11452.IsHomogeneous 24 := by
  unfold a11452
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha10779.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a11453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11420 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11452 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11445 ^ 1)
theorem ha11453 : a11453.IsHomogeneous 30 := by
  unfold a11453
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11420.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11452.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11445.pow 1)))

@[irreducible]
def a11454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11446 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11453 ^ 1)
theorem ha11454 : a11454.IsHomogeneous 30 := by
  unfold a11454
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11446.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11453.pow 1)))

@[irreducible]
def a11455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11447 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a11454 ^ 1)
theorem ha11455 : a11455.IsHomogeneous 30 := by
  unfold a11455
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11447.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha11454.pow 1)))

@[irreducible]
def a11456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11455 ^ 1)
theorem ha11456 : a11456.IsHomogeneous 30 := by
  unfold a11456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11451.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11455.pow 1)))

@[irreducible]
def a11457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a05994 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a11138 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a05994 ^ 1)
theorem ha11457 : a11457.IsHomogeneous 24 := by
  unfold a11457
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha05994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha11138.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha05994.pow 1)))

@[irreducible]
def a11458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11448 ^ 1)
theorem ha11458 : a11458.IsHomogeneous 30 := by
  unfold a11458
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11433.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11457.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11448.pow 1)))

@[irreducible]
def a11459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11434 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11458 ^ 1)
theorem ha11459 : a11459.IsHomogeneous 30 := by
  unfold a11459
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11434.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11449.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11458.pow 1)))

@[irreducible]
def a11460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11450 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11459 ^ 1)
theorem ha11460 : a11460.IsHomogeneous 30 := by
  unfold a11460
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11450.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11459.pow 1)))

@[irreducible]
def a11461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11451 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a11460 ^ 1)
theorem ha11461 : a11461.IsHomogeneous 30 := by
  unfold a11461
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11451.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha11460.pow 1)))

@[irreducible]
def a11462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11461 ^ 1)
theorem ha11462 : a11462.IsHomogeneous 30 := by
  unfold a11462
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11441.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11456.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11461.pow 1)))

@[irreducible]
def a11463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a10903 ^ 1) + (C ((7 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a11462 ^ 1)
theorem ha11463 : a11463.IsHomogeneous 49 := by
  unfold a11463
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha10903.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha11462.pow 1)))

@[irreducible]
def a11464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00506 ^ 1)
theorem ha11464 : a11464.IsHomogeneous 30 := by
  unfold a11464
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1 * a01327 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00555 ^ 1)
theorem ha11465 : a11465.IsHomogeneous 30 := by
  unfold a11465
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a11466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1 * a01327 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a01327 ^ 1)
theorem ha11466 : a11466.IsHomogeneous 30 := by
  unfold a11466
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11464 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a11466 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11465 ^ 1)
theorem ha11467 : a11467.IsHomogeneous 30 := by
  unfold a11467
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha11466.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11465.pow 1)))

@[irreducible]
def a11468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00555 ^ 1)
theorem ha11468 : a11468.IsHomogeneous 30 := by
  unfold a11468
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a11469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00171 ^ 1)
theorem ha11469 : a11469.IsHomogeneous 24 := by
  unfold a11469
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha00555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a11470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11469 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a11464 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a11468 ^ 1)
theorem ha11470 : a11470.IsHomogeneous 30 := by
  unfold a11470
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha11464.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha11468.pow 1)))

@[irreducible]
def a11471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a03116 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a01429 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha11471 : a11471.IsHomogeneous 30 := by
  unfold a11471
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01429.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11465 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11471 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a11468 ^ 1)
theorem ha11472 : a11472.IsHomogeneous 30 := by
  unfold a11472
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11471.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha11468.pow 1)))

@[irreducible]
def a11473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11467 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11472 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11470 ^ 1)
theorem ha11473 : a11473.IsHomogeneous 30 := by
  unfold a11473
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11472.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11470.pow 1)))

@[irreducible]
def a11474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1 * a00506 ^ 1)
theorem ha11474 : a11474.IsHomogeneous 24 := by
  unfold a11474
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a11475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1)
theorem ha11475 : a11475.IsHomogeneous 24 := by
  unfold a11475
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11474 ^ 1) + (C ((1 : ℂ) / (20 : ℂ)) * a11464 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a11475 ^ 1)
theorem ha11476 : a11476.IsHomogeneous 30 := by
  unfold a11476
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11474.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (20 : ℂ))).mul (ha11464.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha11475.pow 1)))

@[irreducible]
def a11477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a02935 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02935 ^ 1)
theorem ha11477 : a11477.IsHomogeneous 24 := by
  unfold a11477
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11475 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11466 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11477 ^ 1)
theorem ha11478 : a11478.IsHomogeneous 30 := by
  unfold a11478
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11475.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11466.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11477.pow 1)))

@[irreducible]
def a11479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11467 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11478 ^ 1) + (C ((20 : ℂ) / (1 : ℂ)) * a11476 ^ 1)
theorem ha11479 : a11479.IsHomogeneous 30 := by
  unfold a11479
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11478.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (1 : ℂ))).mul (ha11476.pow 1)))

@[irreducible]
def a11480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1)
theorem ha11480 : a11480.IsHomogeneous 18 := by
  unfold a11480
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a11481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11469 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11480 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11474 ^ 1)
theorem ha11481 : a11481.IsHomogeneous 24 := by
  unfold a11481
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11480.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11474.pow 1)))

@[irreducible]
def a11482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11470 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11476 ^ 1)
theorem ha11482 : a11482.IsHomogeneous 30 := by
  unfold a11482
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11470.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11476.pow 1)))

@[irreducible]
def a11483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11479 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11482 ^ 1)
theorem ha11483 : a11483.IsHomogeneous 30 := by
  unfold a11483
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11473.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11479.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11482.pow 1)))

@[irreducible]
def a11484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01429 ^ 1)
theorem ha11484 : a11484.IsHomogeneous 18 := by
  unfold a11484
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03116 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01429 ^ 1)
theorem ha11485 : a11485.IsHomogeneous 24 := by
  unfold a11485
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11468 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a11484 ^ 1)
theorem ha11486 : a11486.IsHomogeneous 30 := by
  unfold a11486
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11468.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha11484.pow 1)))

@[irreducible]
def a11487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00171 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00555 ^ 1)
theorem ha11487 : a11487.IsHomogeneous 18 := by
  unfold a11487
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1)))

@[irreducible]
def a11488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11469 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a11487 ^ 1)
theorem ha11488 : a11488.IsHomogeneous 24 := by
  unfold a11488
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11484.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11469.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha11487.pow 1)))

@[irreducible]
def a11489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11488 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11470 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a11486 ^ 1)
theorem ha11489 : a11489.IsHomogeneous 30 := by
  unfold a11489
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11488.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11470.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha11486.pow 1)))

@[irreducible]
def a11490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a03116 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03116 ^ 1)
theorem ha11490 : a11490.IsHomogeneous 24 := by
  unfold a11490
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a11491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11485 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a11490 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11471 ^ 1)
theorem ha11491 : a11491.IsHomogeneous 30 := by
  unfold a11491
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11485.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha11490.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11471.pow 1)))

@[irreducible]
def a11492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11472 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a11486 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a11491 ^ 1)
theorem ha11492 : a11492.IsHomogeneous 30 := by
  unfold a11492
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha11486.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha11491.pow 1)))

@[irreducible]
def a11493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11473 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11492 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11489 ^ 1)
theorem ha11493 : a11493.IsHomogeneous 30 := by
  unfold a11493
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11473.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11492.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11489.pow 1)))

@[irreducible]
def a11494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00171 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha11494 : a11494.IsHomogeneous 12 := by
  unfold a11494
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a11495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11480 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a11487 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a11494 ^ 1)
theorem ha11495 : a11495.IsHomogeneous 18 := by
  unfold a11495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11480.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha11487.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha11494.pow 1)))

@[irreducible]
def a11496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11488 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a11495 ^ 1)
theorem ha11496 : a11496.IsHomogeneous 24 := by
  unfold a11496
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11488.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha11495.pow 1)))

@[irreducible]
def a11497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11496 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11482 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11489 ^ 1)
theorem ha11497 : a11497.IsHomogeneous 30 := by
  unfold a11497
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11482.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11489.pow 1)))

@[irreducible]
def a11498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11493 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a11497 ^ 1)
theorem ha11498 : a11498.IsHomogeneous 30 := by
  unfold a11498
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11493.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha11497.pow 1)))

@[irreducible]
def a11499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00555 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a01327 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00555 ^ 1 * a01327 ^ 1)
theorem ha11499 : a11499.IsHomogeneous 24 := by
  unfold a11499
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha01327.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a11500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01327 ^ 1 * a01429 ^ 1)
theorem ha11500 : a11500.IsHomogeneous 30 := by
  unfold a11500
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01429.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01327.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a11501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11465 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a11499 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11500 ^ 1)
theorem ha11501 : a11501.IsHomogeneous 30 := by
  unfold a11501
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11465.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha11499.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11500.pow 1)))

@[irreducible]
def a11502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02935 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a02935 ^ 1)
theorem ha11502 : a11502.IsHomogeneous 30 := by
  unfold a11502
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a11503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11466 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a11502 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a11499 ^ 1)
theorem ha11503 : a11503.IsHomogeneous 30 := by
  unfold a11503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11466.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha11502.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha11499.pow 1)))

@[irreducible]
def a11504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11467 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a11503 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11501 ^ 1)
theorem ha11504 : a11504.IsHomogeneous 30 := by
  unfold a11504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha11503.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11501.pow 1)))

@[irreducible]
def a11505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a06044 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a03116 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a03116 ^ 1)
theorem ha11505 : a11505.IsHomogeneous 30 := by
  unfold a11505
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha06044.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a11506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11471 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11505 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a11500 ^ 1)
theorem ha11506 : a11506.IsHomogeneous 30 := by
  unfold a11506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11471.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11505.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha11500.pow 1)))

@[irreducible]
def a11507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11472 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11501 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a11506 ^ 1)
theorem ha11507 : a11507.IsHomogeneous 30 := by
  unfold a11507
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11472.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11501.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha11506.pow 1)))

@[irreducible]
def a11508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11504 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11507 ^ 1)
theorem ha11508 : a11508.IsHomogeneous 30 := by
  unfold a11508
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11473.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11504.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11507.pow 1)))

@[irreducible]
def a11509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a10779 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a05754 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a05754 ^ 1)
theorem ha11509 : a11509.IsHomogeneous 24 := by
  unfold a11509
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha10779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a11510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11477 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11502 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11509 ^ 1)
theorem ha11510 : a11510.IsHomogeneous 30 := by
  unfold a11510
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11477.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11502.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11509.pow 1)))

@[irreducible]
def a11511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11478 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a11503 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11510 ^ 1)
theorem ha11511 : a11511.IsHomogeneous 30 := by
  unfold a11511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha11503.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11510.pow 1)))

@[irreducible]
def a11512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11504 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a11511 ^ 1)
theorem ha11512 : a11512.IsHomogeneous 30 := by
  unfold a11512
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11479.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11504.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha11511.pow 1)))

@[irreducible]
def a11513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11512 ^ 1)
theorem ha11513 : a11513.IsHomogeneous 30 := by
  unfold a11513
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11508.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11512.pow 1)))

@[irreducible]
def a11514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a11215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a06044 ^ 1)
theorem ha11514 : a11514.IsHomogeneous 24 := by
  unfold a11514
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha11215.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha06044.pow 1)))

@[irreducible]
def a11515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11490 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a11514 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a11505 ^ 1)
theorem ha11515 : a11515.IsHomogeneous 30 := by
  unfold a11515
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11490.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha11514.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha11505.pow 1)))

@[irreducible]
def a11516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11491 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11506 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a11515 ^ 1)
theorem ha11516 : a11516.IsHomogeneous 30 := by
  unfold a11516
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11506.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha11515.pow 1)))

@[irreducible]
def a11517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11507 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a11516 ^ 1)
theorem ha11517 : a11517.IsHomogeneous 30 := by
  unfold a11517
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11507.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha11516.pow 1)))

@[irreducible]
def a11518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11493 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11508 ^ 1) + (C ((20 : ℂ) / (7 : ℂ)) * a11517 ^ 1)
theorem ha11518 : a11518.IsHomogeneous 30 := by
  unfold a11518
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11508.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (7 : ℂ))).mul (ha11517.pow 1)))

@[irreducible]
def a11519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11513 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11518 ^ 1)
theorem ha11519 : a11519.IsHomogeneous 30 := by
  unfold a11519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11498.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11513.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11518.pow 1)))

end CycleQ2Concrete
