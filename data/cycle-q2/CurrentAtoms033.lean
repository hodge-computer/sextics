import Proposal.CurrentAtoms032

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a10240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10239 ^ 1)
theorem ha10240 : a10240.IsHomogeneous 138 := by
  unfold a10240
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10239.pow 1)))

@[irreducible]
def a10241 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10228 ^ 1)
theorem ha10241 : a10241.IsHomogeneous 141 := by
  unfold a10241
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10240.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10228.pow 1)))

@[irreducible]
def a10242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a07312 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00455 ^ 1 * a03933 ^ 1)
theorem ha10242 : a10242.IsHomogeneous 141 := by
  unfold a10242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha07312.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00455.pow 1)).mul (ha03933.pow 1)))

@[irreducible]
def a10243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10224 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a10242 ^ 1)
theorem ha10243 : a10243.IsHomogeneous 141 := by
  unfold a10243
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10224.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha10242.pow 1)))

@[irreducible]
def a10244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10243 ^ 1)
theorem ha10244 : a10244.IsHomogeneous 141 := by
  unfold a10244
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10243.pow 1)))

@[irreducible]
def a10245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10244 ^ 1)
theorem ha10245 : a10245.IsHomogeneous 141 := by
  unfold a10245
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10228.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10244.pow 1)))

@[irreducible]
def a10246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10245 ^ 1)
theorem ha10246 : a10246.IsHomogeneous 141 := by
  unfold a10246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10245.pow 1)))

@[irreducible]
def a10247 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00809 ^ 1 * a02814 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01264 ^ 1 * a01896 ^ 1)
theorem ha10247 : a10247.IsHomogeneous 178 := by
  unfold a10247
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00809.pow 1)).mul (ha02814.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01264.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a10248 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00480 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01264 ^ 1 * a01896 ^ 1)
theorem ha10248 : a10248.IsHomogeneous 172 := by
  unfold a10248
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00480.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01264.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a10249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10247 ^ 1)
theorem ha10249 : a10249.IsHomogeneous 178 := by
  unfold a10249
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10248.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10247.pow 1)))

@[irreducible]
def a10250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a02814 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a05555 ^ 1)
theorem ha10250 : a10250.IsHomogeneous 185 := by
  unfold a10250
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha02814.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha05555.pow 1)))

@[irreducible]
def a10251 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a10250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10247 ^ 1)
theorem ha10251 : a10251.IsHomogeneous 185 := by
  unfold a10251
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha10250.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10247.pow 1)))

@[irreducible]
def a10252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10251 ^ 1)
theorem ha10252 : a10252.IsHomogeneous 185 := by
  unfold a10252
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10251.pow 1)))

@[irreducible]
def a10253 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00148 ^ 1 * a07248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00480 ^ 1 * a03890 ^ 1)
theorem ha10253 : a10253.IsHomogeneous 166 := by
  unfold a10253
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00480.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a10254 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a10253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10248 ^ 1)
theorem ha10254 : a10254.IsHomogeneous 172 := by
  unfold a10254
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha10253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10248.pow 1)))

@[irreducible]
def a10255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10249 ^ 1)
theorem ha10255 : a10255.IsHomogeneous 178 := by
  unfold a10255
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10254.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10249.pow 1)))

@[irreducible]
def a10256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a10255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10252 ^ 1)
theorem ha10256 : a10256.IsHomogeneous 185 := by
  unfold a10256
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha10255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10252.pow 1)))

@[irreducible]
def a10257 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a00829 ^ 1 * a02744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01223 ^ 1 * a01938 ^ 1)
theorem ha10257 : a10257.IsHomogeneous 141 := by
  unfold a10257
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha00829.pow 1)).mul (ha02744.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01223.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a10258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01223 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a03963 ^ 1)
theorem ha10258 : a10258.IsHomogeneous 144 := by
  unfold a10258
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01223.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a10259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10257 ^ 1)
theorem ha10259 : a10259.IsHomogeneous 147 := by
  unfold a10259
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10258.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10257.pow 1)))

@[irreducible]
def a10260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a05448 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a02744 ^ 1)
theorem ha10260 : a10260.IsHomogeneous 135 := by
  unfold a10260
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha05448.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha02744.pow 1)))

@[irreducible]
def a10261 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00014 ^ 1 * a10260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10257 ^ 1)
theorem ha10261 : a10261.IsHomogeneous 141 := by
  unfold a10261
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00014.pow 1)).mul (ha10260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10257.pow 1)))

@[irreducible]
def a10262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10259 ^ 1)
theorem ha10262 : a10262.IsHomogeneous 147 := by
  unfold a10262
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10261.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10259.pow 1)))

@[irreducible]
def a10263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a01213 ^ 1)
theorem ha10263 : a10263.IsHomogeneous 45 := by
  unfold a10263
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha01213.pow 1)))

@[irreducible]
def a10264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01213 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a02724 ^ 1)
theorem ha10264 : a10264.IsHomogeneous 45 := by
  unfold a10264
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha02724.pow 1)))

@[irreducible]
def a10265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10263 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a10264 ^ 1)
theorem ha10265 : a10265.IsHomogeneous 45 := by
  unfold a10265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10263.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha10264.pow 1)))

@[irreducible]
def a10266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha10266 : a10266.IsHomogeneous 24 := by
  unfold a10266
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a10267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a10266 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10263 ^ 1)
theorem ha10267 : a10267.IsHomogeneous 48 := by
  unfold a10267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha10266.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10263.pow 1)))

@[irreducible]
def a10268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10267 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10265 ^ 1)
theorem ha10268 : a10268.IsHomogeneous 48 := by
  unfold a10268
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10267.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10265.pow 1)))

@[irreducible]
def a10269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02724 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a05415 ^ 1)
theorem ha10269 : a10269.IsHomogeneous 45 := by
  unfold a10269
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02724.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha05415.pow 1)))

@[irreducible]
def a10270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10264 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a10269 ^ 1)
theorem ha10270 : a10270.IsHomogeneous 45 := by
  unfold a10270
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha10269.pow 1)))

@[irreducible]
def a10271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10265 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a10270 ^ 1)
theorem ha10271 : a10271.IsHomogeneous 45 := by
  unfold a10271
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha10270.pow 1)))

@[irreducible]
def a10272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10268 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10271 ^ 1)
theorem ha10272 : a10272.IsHomogeneous 48 := by
  unfold a10272
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10268.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10271.pow 1)))

@[irreducible]
def a10273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02008 ^ 1)
theorem ha10273 : a10273.IsHomogeneous 42 := by
  unfold a10273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a10274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10273 ^ 1)
theorem ha10274 : a10274.IsHomogeneous 42 := by
  unfold a10274
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00865.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10273.pow 1)))

@[irreducible]
def a10275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a04086 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02008 ^ 1)
theorem ha10275 : a10275.IsHomogeneous 42 := by
  unfold a10275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a10276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10273 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a10275 ^ 1)
theorem ha10276 : a10276.IsHomogeneous 42 := by
  unfold a10276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha10275.pow 1)))

@[irreducible]
def a10277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10274 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10276 ^ 1)
theorem ha10277 : a10277.IsHomogeneous 42 := by
  unfold a10277
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10274.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10276.pow 1)))

@[irreducible]
def a10278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10274 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10277 ^ 1)
theorem ha10278 : a10278.IsHomogeneous 42 := by
  unfold a10278
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10274.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10277.pow 1)))

@[irreducible]
def a10279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a10278 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a05415 ^ 1)
theorem ha10279 : a10279.IsHomogeneous 48 := by
  unfold a10279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha10278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha05415.pow 1)))

@[irreducible]
def a10280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10279 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a10269 ^ 1)
theorem ha10280 : a10280.IsHomogeneous 48 := by
  unfold a10280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10279.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha10269.pow 1)))

@[irreducible]
def a10281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10280 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a10270 ^ 1)
theorem ha10281 : a10281.IsHomogeneous 48 := by
  unfold a10281
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha10270.pow 1)))

@[irreducible]
def a10282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10281 ^ 1) + (C ((1 : ℂ) / (20 : ℂ)) * a00003 ^ 3 * a10271 ^ 1)
theorem ha10282 : a10282.IsHomogeneous 48 := by
  unfold a10282
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10281.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (20 : ℂ))).mul (ha00003.pow 3)).mul (ha10271.pow 1)))

@[irreducible]
def a10283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10272 ^ 1) + (C ((360 : ℂ) / (1 : ℂ)) * a10282 ^ 1)
theorem ha10283 : a10283.IsHomogeneous 48 := by
  unfold a10283
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((360 : ℂ) / (1 : ℂ))).mul (ha10282.pow 1)))

@[irreducible]
def a10284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00317 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00324 ^ 1)
theorem ha10284 : a10284.IsHomogeneous 27 := by
  unfold a10284
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a10285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00130 ^ 1)
theorem ha10285 : a10285.IsHomogeneous 33 := by
  unfold a10285
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a10286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00317 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha10286 : a10286.IsHomogeneous 33 := by
  unfold a10286
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a10287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10285 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a10284 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10286 ^ 1)
theorem ha10287 : a10287.IsHomogeneous 33 := by
  unfold a10287
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10285.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha10284.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10286.pow 1)))

@[irreducible]
def a10288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1)
theorem ha10288 : a10288.IsHomogeneous 30 := by
  unfold a10288
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00324.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)))

@[irreducible]
def a10289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00324 ^ 1)
theorem ha10289 : a10289.IsHomogeneous 30 := by
  unfold a10289
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a10290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10288 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10289 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10284 ^ 1)
theorem ha10290 : a10290.IsHomogeneous 30 := by
  unfold a10290
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10289.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10284.pow 1)))

@[irreducible]
def a10291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10285 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01593 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a10288 ^ 1)
theorem ha10291 : a10291.IsHomogeneous 33 := by
  unfold a10291
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10285.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01593.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha10288.pow 1)))

@[irreducible]
def a10292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10287 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10291 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a10290 ^ 1)
theorem ha10292 : a10292.IsHomogeneous 33 := by
  unfold a10292
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10287.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10291.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha10290.pow 1)))

@[irreducible]
def a10293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00865 ^ 1)
theorem ha10293 : a10293.IsHomogeneous 27 := by
  unfold a10293
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a10294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00133 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00032 ^ 1 * a00317 ^ 1)
theorem ha10294 : a10294.IsHomogeneous 27 := by
  unfold a10294
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a10295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10284 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a10294 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a10293 ^ 1)
theorem ha10295 : a10295.IsHomogeneous 27 := by
  unfold a10295
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10284.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha10294.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha10293.pow 1)))

@[irreducible]
def a10296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00865 ^ 1)
theorem ha10296 : a10296.IsHomogeneous 33 := by
  unfold a10296
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a10297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10296 ^ 1) + (C ((35 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a10293 ^ 1)
theorem ha10297 : a10297.IsHomogeneous 33 := by
  unfold a10297
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10296.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha10293.pow 1)))

@[irreducible]
def a10298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10287 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a10295 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10297 ^ 1)
theorem ha10298 : a10298.IsHomogeneous 33 := by
  unfold a10298
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10287.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha10295.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10297.pow 1)))

@[irreducible]
def a10299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1)
theorem ha10299 : a10299.IsHomogeneous 30 := by
  unfold a10299
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a10300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10289 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a10299 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10294 ^ 1)
theorem ha10300 : a10300.IsHomogeneous 30 := by
  unfold a10300
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10289.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha10299.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10294.pow 1)))

@[irreducible]
def a10301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10290 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10300 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10295 ^ 1)
theorem ha10301 : a10301.IsHomogeneous 30 := by
  unfold a10301
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10300.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10295.pow 1)))

@[irreducible]
def a10302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10298 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a10301 ^ 1)
theorem ha10302 : a10302.IsHomogeneous 33 := by
  unfold a10302
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10298.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha10301.pow 1)))

@[irreducible]
def a10303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00317 ^ 1)
theorem ha10303 : a10303.IsHomogeneous 33 := by
  unfold a10303
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a10304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10285 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a10303 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01595 ^ 1)
theorem ha10304 : a10304.IsHomogeneous 33 := by
  unfold a10304
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha10303.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01595.pow 1)))

@[irreducible]
def a10305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00133 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00133 ^ 1 * a00865 ^ 1)
theorem ha10305 : a10305.IsHomogeneous 33 := by
  unfold a10305
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a10306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10286 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a10303 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a10305 ^ 1)
theorem ha10306 : a10306.IsHomogeneous 33 := by
  unfold a10306
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha10303.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha10305.pow 1)))

@[irreducible]
def a10307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10287 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10304 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10306 ^ 1)
theorem ha10307 : a10307.IsHomogeneous 33 := by
  unfold a10307
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10287.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10304.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10306.pow 1)))

@[irreducible]
def a10308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10304 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01596 ^ 1)
theorem ha10308 : a10308.IsHomogeneous 33 := by
  unfold a10308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10304.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01596.pow 1)))

@[irreducible]
def a10309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10308 ^ 1)
theorem ha10309 : a10309.IsHomogeneous 33 := by
  unfold a10309
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10307.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10308.pow 1)))

@[irreducible]
def a10310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a02008 ^ 1)
theorem ha10310 : a10310.IsHomogeneous 30 := by
  unfold a10310
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha02008.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a10311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10296 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a10310 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a10305 ^ 1)
theorem ha10311 : a10311.IsHomogeneous 33 := by
  unfold a10311
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10296.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha10310.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha10305.pow 1)))

@[irreducible]
def a10312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10297 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10306 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10311 ^ 1)
theorem ha10312 : a10312.IsHomogeneous 33 := by
  unfold a10312
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10297.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10306.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10311.pow 1)))

@[irreducible]
def a10313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10307 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a10312 ^ 1)
theorem ha10313 : a10313.IsHomogeneous 33 := by
  unfold a10313
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10307.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha10312.pow 1)))

@[irreducible]
def a10314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10313 ^ 1)
theorem ha10314 : a10314.IsHomogeneous 33 := by
  unfold a10314
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10302.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10309.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10313.pow 1)))

@[irreducible]
def a10315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a01607 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00649 ^ 1)
theorem ha10315 : a10315.IsHomogeneous 18 := by
  unfold a10315
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha01607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00649.pow 1)))

@[irreducible]
def a10316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10315 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a01604 ^ 1)
theorem ha10316 : a10316.IsHomogeneous 18 := by
  unfold a10316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10315.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha01604.pow 1)))

@[irreducible]
def a10317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a03417 ^ 1) + (C ((7 : ℂ) / (8 : ℂ)) * a00324 ^ 1 * a01607 ^ 1)
theorem ha10317 : a10317.IsHomogeneous 18 := by
  unfold a10317
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha03417.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (8 : ℂ))).mul (ha00324.pow 1)).mul (ha01607.pow 1)))

@[irreducible]
def a10318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10315 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a10317 ^ 1)
theorem ha10318 : a10318.IsHomogeneous 18 := by
  unfold a10318
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10315.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha10317.pow 1)))

@[irreducible]
def a10319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10318 ^ 1)
theorem ha10319 : a10319.IsHomogeneous 18 := by
  unfold a10319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10318.pow 1)))

@[irreducible]
def a10320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10316 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a01605 ^ 1)
theorem ha10320 : a10320.IsHomogeneous 18 := by
  unfold a10320
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha01605.pow 1)))

@[irreducible]
def a10321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10320 ^ 1)
theorem ha10321 : a10321.IsHomogeneous 18 := by
  unfold a10321
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10320.pow 1)))

@[irreducible]
def a10322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a03417 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a06508 ^ 1)
theorem ha10322 : a10322.IsHomogeneous 18 := by
  unfold a10322
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha03417.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha06508.pow 1)))

@[irreducible]
def a10323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10322 ^ 1)
theorem ha10323 : a10323.IsHomogeneous 18 := by
  unfold a10323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10322.pow 1)))

@[irreducible]
def a10324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10318 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a10323 ^ 1)
theorem ha10324 : a10324.IsHomogeneous 18 := by
  unfold a10324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10318.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha10323.pow 1)))

@[irreducible]
def a10325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10324 ^ 1)
theorem ha10325 : a10325.IsHomogeneous 18 := by
  unfold a10325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10324.pow 1)))

@[irreducible]
def a10326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10325 ^ 1)
theorem ha10326 : a10326.IsHomogeneous 18 := by
  unfold a10326
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10325.pow 1)))

@[irreducible]
def a10327 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a10314 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10283 ^ 1) + (C ((49 : ℂ) / (58320 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00004 ^ 6 * a10326 ^ 1)
theorem ha10327 : a10327.IsHomogeneous 48 := by
  unfold a10327
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha10314.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10283.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((49 : ℂ) / (58320 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00004.pow 6)).mul (ha10326.pow 1)))

@[irreducible]
def a10328 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a10327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05448 ^ 1)
theorem ha10328 : a10328.IsHomogeneous 90 := by
  unfold a10328
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05448.pow 1)))

@[irreducible]
def a10329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10260 ^ 1)
theorem ha10329 : a10329.IsHomogeneous 135 := by
  unfold a10329
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10260.pow 1)))

@[irreducible]
def a10330 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00014 ^ 1 * a10329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10261 ^ 1)
theorem ha10330 : a10330.IsHomogeneous 141 := by
  unfold a10330
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00014.pow 1)).mul (ha10329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10261.pow 1)))

@[irreducible]
def a10331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10262 ^ 1)
theorem ha10331 : a10331.IsHomogeneous 147 := by
  unfold a10331
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10262.pow 1)))

@[irreducible]
def a10332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a07363 ^ 1)
theorem ha10332 : a10332.IsHomogeneous 153 := by
  unfold a10332
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a10333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a10258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10332 ^ 1)
theorem ha10333 : a10333.IsHomogeneous 153 := by
  unfold a10333
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha10258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10332.pow 1)))

@[irreducible]
def a10334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10333 ^ 1)
theorem ha10334 : a10334.IsHomogeneous 153 := by
  unfold a10334
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10333.pow 1)))

@[irreducible]
def a10335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10334 ^ 1)
theorem ha10335 : a10335.IsHomogeneous 153 := by
  unfold a10335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10334.pow 1)))

@[irreducible]
def a10336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10331 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10335 ^ 1)
theorem ha10336 : a10336.IsHomogeneous 153 := by
  unfold a10336
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10331.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10335.pow 1)))

@[irreducible]
def a10337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01261 ^ 1 * a01841 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00155 ^ 1 * a02810 ^ 1)
theorem ha10337 : a10337.IsHomogeneous 145 := by
  unfold a10337
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01261.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha02810.pow 1)))

@[irreducible]
def a10338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00478 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01261 ^ 1 * a01841 ^ 1)
theorem ha10338 : a10338.IsHomogeneous 145 := by
  unfold a10338
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00478.pow 1)).mul (ha03803.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01261.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a10339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10337 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10338 ^ 1)
theorem ha10339 : a10339.IsHomogeneous 145 := by
  unfold a10339
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10338.pow 1)))

@[irreducible]
def a10340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02810 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a05550 ^ 1)
theorem ha10340 : a10340.IsHomogeneous 137 := by
  unfold a10340
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02810.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha05550.pow 1)))

@[irreducible]
def a10341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10337 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a10340 ^ 1)
theorem ha10341 : a10341.IsHomogeneous 145 := by
  unfold a10341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10337.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha10340.pow 1)))

@[irreducible]
def a10342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10341 ^ 1)
theorem ha10342 : a10342.IsHomogeneous 145 := by
  unfold a10342
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10339.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10341.pow 1)))

@[irreducible]
def a10343 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00478 ^ 1 * a03803 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00147 ^ 1 * a07120 ^ 1)
theorem ha10343 : a10343.IsHomogeneous 145 := by
  unfold a10343
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00478.pow 1)).mul (ha03803.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00147.pow 1)).mul (ha07120.pow 1)))

@[irreducible]
def a10344 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a10343 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10338 ^ 1)
theorem ha10344 : a10344.IsHomogeneous 145 := by
  unfold a10344
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha10343.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10338.pow 1)))

@[irreducible]
def a10345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10339 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a10344 ^ 1)
theorem ha10345 : a10345.IsHomogeneous 145 := by
  unfold a10345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10339.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha10344.pow 1)))

@[irreducible]
def a10346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10345 ^ 1)
theorem ha10346 : a10346.IsHomogeneous 145 := by
  unfold a10346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10342.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10345.pow 1)))

@[irreducible]
def a10347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01228 ^ 1 * a01917 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a02754 ^ 1)
theorem ha10347 : a10347.IsHomogeneous 123 := by
  unfold a10347
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01228.pow 1)).mul (ha01917.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a10348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a03925 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01228 ^ 1 * a01917 ^ 1)
theorem ha10348 : a10348.IsHomogeneous 120 := by
  unfold a10348
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha03925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01228.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a10349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10347 ^ 1)
theorem ha10349 : a10349.IsHomogeneous 123 := by
  unfold a10349
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10347.pow 1)))

@[irreducible]
def a10350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00301 ^ 1 * a03811 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a02754 ^ 1)
theorem ha10350 : a10350.IsHomogeneous 117 := by
  unfold a10350
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a10351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10350 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a10347 ^ 1)
theorem ha10351 : a10351.IsHomogeneous 123 := by
  unfold a10351
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha10347.pow 1)))

@[irreducible]
def a10352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10349 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a10351 ^ 1)
theorem ha10352 : a10352.IsHomogeneous 123 := by
  unfold a10352
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10349.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha10351.pow 1)))

@[irreducible]
def a10353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a07269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10350 ^ 1)
theorem ha10353 : a10353.IsHomogeneous 117 := by
  unfold a10353
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha07269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10350.pow 1)))

@[irreducible]
def a10354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10351 ^ 1)
theorem ha10354 : a10354.IsHomogeneous 123 := by
  unfold a10354
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10351.pow 1)))

@[irreducible]
def a10355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10352 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a10354 ^ 1)
theorem ha10355 : a10355.IsHomogeneous 123 := by
  unfold a10355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha10354.pow 1)))

@[irreducible]
def a10356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00461 ^ 1 * a03925 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00138 ^ 1 * a07302 ^ 1)
theorem ha10356 : a10356.IsHomogeneous 123 := by
  unfold a10356
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00461.pow 1)).mul (ha03925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00138.pow 1)).mul (ha07302.pow 1)))

@[irreducible]
def a10357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10356 ^ 1)
theorem ha10357 : a10357.IsHomogeneous 123 := by
  unfold a10357
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10356.pow 1)))

@[irreducible]
def a10358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10349 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10357 ^ 1)
theorem ha10358 : a10358.IsHomogeneous 123 := by
  unfold a10358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10349.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10357.pow 1)))

@[irreducible]
def a10359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10358 ^ 1)
theorem ha10359 : a10359.IsHomogeneous 123 := by
  unfold a10359
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10358.pow 1)))

@[irreducible]
def a10360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10355 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10359 ^ 1)
theorem ha10360 : a10360.IsHomogeneous 123 := by
  unfold a10360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10355.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10359.pow 1)))

@[irreducible]
def a10361 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a01258 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00812 ^ 1 * a02806 ^ 1)
theorem ha10361 : a10361.IsHomogeneous 124 := by
  unfold a10361
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha01258.pow 1)).mul (ha01903.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00812.pow 1)).mul (ha02806.pow 1)))

@[irreducible]
def a10362 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a01258 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00476 ^ 1 * a03811 ^ 1)
theorem ha10362 : a10362.IsHomogeneous 124 := by
  unfold a10362
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha01258.pow 1)).mul (ha01903.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a10363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10361 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a10362 ^ 1)
theorem ha10363 : a10363.IsHomogeneous 124 := by
  unfold a10363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha10362.pow 1)))

@[irreducible]
def a10364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a05545 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00812 ^ 1 * a02806 ^ 1)
theorem ha10364 : a10364.IsHomogeneous 122 := by
  unfold a10364
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha05545.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00812.pow 1)).mul (ha02806.pow 1)))

@[irreducible]
def a10365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10364 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a10361 ^ 1)
theorem ha10365 : a10365.IsHomogeneous 124 := by
  unfold a10365
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha10361.pow 1)))

@[irreducible]
def a10366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a10365 ^ 1)
theorem ha10366 : a10366.IsHomogeneous 124 := by
  unfold a10366
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha10365.pow 1)))

@[irreducible]
def a10367 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a07132 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a03811 ^ 1)
theorem ha10367 : a10367.IsHomogeneous 109 := by
  unfold a10367
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha07132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a10368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a10367 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10362 ^ 1)
theorem ha10368 : a10368.IsHomogeneous 124 := by
  unfold a10368
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha10367.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10362.pow 1)))

@[irreducible]
def a10369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10363 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a10368 ^ 1)
theorem ha10369 : a10369.IsHomogeneous 124 := by
  unfold a10369
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha10368.pow 1)))

@[irreducible]
def a10370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10366 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10369 ^ 1)
theorem ha10370 : a10370.IsHomogeneous 124 := by
  unfold a10370
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10366.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10369.pow 1)))

@[irreducible]
def a10371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02778 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01240 ^ 1 * a01702 ^ 1)
theorem ha10371 : a10371.IsHomogeneous 90 := by
  unfold a10371
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02778.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01240.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a10372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01240 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00465 ^ 1 * a03562 ^ 1)
theorem ha10372 : a10372.IsHomogeneous 93 := by
  unfold a10372
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01240.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00465.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10372 ^ 1)
theorem ha10373 : a10373.IsHomogeneous 93 := by
  unfold a10373
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10372.pow 1)))

@[irreducible]
def a10374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02778 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a05504 ^ 1)
theorem ha10374 : a10374.IsHomogeneous 93 := by
  unfold a10374
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02778.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha05504.pow 1)))

@[irreducible]
def a10375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10374 ^ 1)
theorem ha10375 : a10375.IsHomogeneous 93 := by
  unfold a10375
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10374.pow 1)))

@[irreducible]
def a10376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10375 ^ 1)
theorem ha10376 : a10376.IsHomogeneous 93 := by
  unfold a10376
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10373.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10375.pow 1)))

@[irreducible]
def a10377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00139 ^ 1 * a06725 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00465 ^ 1 * a03562 ^ 1)
theorem ha10377 : a10377.IsHomogeneous 87 := by
  unfold a10377
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00139.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00465.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10372 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10377 ^ 1)
theorem ha10378 : a10378.IsHomogeneous 93 := by
  unfold a10378
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10377.pow 1)))

@[irreducible]
def a10379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10378 ^ 1)
theorem ha10379 : a10379.IsHomogeneous 93 := by
  unfold a10379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10373.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10378.pow 1)))

@[irreducible]
def a10380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10379 ^ 1)
theorem ha10380 : a10380.IsHomogeneous 93 := by
  unfold a10380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10379.pow 1)))

@[irreducible]
def a10381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01207 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02710 ^ 1)
theorem ha10381 : a10381.IsHomogeneous 39 := by
  unfold a10381
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1 * a02008 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00865 ^ 1 * a01207 ^ 1)
theorem ha10382 : a10382.IsHomogeneous 36 := by
  unfold a10382
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00865.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a10383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10382 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a10381 ^ 1)
theorem ha10383 : a10383.IsHomogeneous 42 := by
  unfold a10383
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10382.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha10381.pow 1)))

@[irreducible]
def a10384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a05389 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a00317 ^ 1 * a02710 ^ 1)
theorem ha10384 : a10384.IsHomogeneous 39 := by
  unfold a10384
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha00317.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10381 ^ 1) + (C ((14 : ℂ) / (15 : ℂ)) * a10384 ^ 1)
theorem ha10385 : a10385.IsHomogeneous 39 := by
  unfold a10385
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (15 : ℂ))).mul (ha10384.pow 1)))

@[irreducible]
def a10386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10383 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a10385 ^ 1)
theorem ha10386 : a10386.IsHomogeneous 42 := by
  unfold a10386
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10383.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha10385.pow 1)))

@[irreducible]
def a10387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a04086 ^ 1)
theorem ha10387 : a10387.IsHomogeneous 30 := by
  unfold a10387
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a10388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10382 ^ 1)
theorem ha10388 : a10388.IsHomogeneous 36 := by
  unfold a10388
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10382.pow 1)))

@[irreducible]
def a10389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10383 ^ 1)
theorem ha10389 : a10389.IsHomogeneous 42 := by
  unfold a10389
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10383.pow 1)))

@[irreducible]
def a10390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10389 ^ 1)
theorem ha10390 : a10390.IsHomogeneous 42 := by
  unfold a10390
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10389.pow 1)))

@[irreducible]
def a10391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a10237 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a05389 ^ 1)
theorem ha10391 : a10391.IsHomogeneous 42 := by
  unfold a10391
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha10237.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a10392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10391 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10384 ^ 1)
theorem ha10392 : a10392.IsHomogeneous 42 := by
  unfold a10392
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10391.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10384.pow 1)))

@[irreducible]
def a10393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10392 ^ 1) + (C ((45 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10385 ^ 1)
theorem ha10393 : a10393.IsHomogeneous 42 := by
  unfold a10393
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10385.pow 1)))

@[irreducible]
def a10394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10386 ^ 1) + (C ((7 : ℂ) / (27 : ℂ)) * a10393 ^ 1)
theorem ha10394 : a10394.IsHomogeneous 42 := by
  unfold a10394
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (27 : ℂ))).mul (ha10393.pow 1)))

@[irreducible]
def a10395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10394 ^ 1)
theorem ha10395 : a10395.IsHomogeneous 42 := by
  unfold a10395
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10394.pow 1)))

@[irreducible]
def a10396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a01896 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a00864 ^ 1)
theorem ha10396 : a10396.IsHomogeneous 39 := by
  unfold a10396
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a03890 ^ 1)
theorem ha10397 : a10397.IsHomogeneous 33 := by
  unfold a10397
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a10398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10396 ^ 1)
theorem ha10398 : a10398.IsHomogeneous 39 := by
  unfold a10398
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10396.pow 1)))

@[irreducible]
def a10399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a00864 ^ 1)
theorem ha10399 : a10399.IsHomogeneous 42 := by
  unfold a10399
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a10400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10399 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10396 ^ 1)
theorem ha10400 : a10400.IsHomogeneous 42 := by
  unfold a10400
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10399.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10396.pow 1)))

@[irreducible]
def a10401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10400 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10398 ^ 1)
theorem ha10401 : a10401.IsHomogeneous 42 := by
  unfold a10401
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10400.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10398.pow 1)))

@[irreducible]
def a10402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04085 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02007 ^ 1)
theorem ha10402 : a10402.IsHomogeneous 42 := by
  unfold a10402
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10399 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a10402 ^ 1)
theorem ha10403 : a10403.IsHomogeneous 42 := by
  unfold a10403
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10399.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha10402.pow 1)))

@[irreducible]
def a10404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10403 ^ 1)
theorem ha10404 : a10404.IsHomogeneous 42 := by
  unfold a10404
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10400.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10403.pow 1)))

@[irreducible]
def a10405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10401 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10404 ^ 1)
theorem ha10405 : a10405.IsHomogeneous 42 := by
  unfold a10405
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10404.pow 1)))

@[irreducible]
def a10406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07248 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03890 ^ 1)
theorem ha10406 : a10406.IsHomogeneous 30 := by
  unfold a10406
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03890.pow 1)))

@[irreducible]
def a10407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10406 ^ 1) + (C ((135 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10397 ^ 1)
theorem ha10407 : a10407.IsHomogeneous 36 := by
  unfold a10407
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10406.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10397.pow 1)))

@[irreducible]
def a10408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10407 ^ 1) + (C ((135 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10398 ^ 1)
theorem ha10408 : a10408.IsHomogeneous 42 := by
  unfold a10408
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10407.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((135 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10398.pow 1)))

@[irreducible]
def a10409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10401 ^ 1) + (C ((7 : ℂ) / (27 : ℂ)) * a10408 ^ 1)
theorem ha10409 : a10409.IsHomogeneous 42 := by
  unfold a10409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (27 : ℂ))).mul (ha10408.pow 1)))

@[irreducible]
def a10410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10405 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10409 ^ 1)
theorem ha10410 : a10410.IsHomogeneous 42 := by
  unfold a10410
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10405.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10409.pow 1)))

@[irreducible]
def a10411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10395 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a10410 ^ 1)
theorem ha10411 : a10411.IsHomogeneous 42 := by
  unfold a10411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10395.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha10410.pow 1)))

@[irreducible]
def a10412 : Poly := (C ((-15 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a05504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10411 ^ 1)
theorem ha10412 : a10412.IsHomogeneous 87 := by
  unfold a10412
  exact ((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha05504.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10411.pow 1)))

@[irreducible]
def a10413 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10374 ^ 1)
theorem ha10413 : a10413.IsHomogeneous 93 := by
  unfold a10413
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10374.pow 1)))

@[irreducible]
def a10414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10413 ^ 1)
theorem ha10414 : a10414.IsHomogeneous 93 := by
  unfold a10414
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10375.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10413.pow 1)))

@[irreducible]
def a10415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10414 ^ 1)
theorem ha10415 : a10415.IsHomogeneous 93 := by
  unfold a10415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10414.pow 1)))

@[irreducible]
def a10416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10380 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10415 ^ 1)
theorem ha10416 : a10416.IsHomogeneous 93 := by
  unfold a10416
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10380.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10415.pow 1)))

@[irreducible]
def a10417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00817 ^ 1 * a01678 ^ 1)
theorem ha10417 : a10417.IsHomogeneous 104 := by
  unfold a10417
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00817.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a10418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a03534 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00817 ^ 1 * a01678 ^ 1)
theorem ha10418 : a10418.IsHomogeneous 104 := by
  unfold a10418
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha03534.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00817.pow 1)).mul (ha01678.pow 1)))

@[irreducible]
def a10419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10417 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a10418 ^ 1)
theorem ha10419 : a10419.IsHomogeneous 104 := by
  unfold a10419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha10418.pow 1)))

@[irreducible]
def a10420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01914 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00241 ^ 1 * a03921 ^ 1)
theorem ha10420 : a10420.IsHomogeneous 106 := by
  unfold a10420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01914.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha03921.pow 1)))

@[irreducible]
def a10421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10420 ^ 1)
theorem ha10421 : a10421.IsHomogeneous 106 := by
  unfold a10421
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10420.pow 1)))

@[irreducible]
def a10422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10421 ^ 1)
theorem ha10422 : a10422.IsHomogeneous 106 := by
  unfold a10422
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10421.pow 1)))

@[irreducible]
def a10423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a06692 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a03534 ^ 1)
theorem ha10423 : a10423.IsHomogeneous 104 := by
  unfold a10423
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha06692.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a10424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10418 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a10423 ^ 1)
theorem ha10424 : a10424.IsHomogeneous 104 := by
  unfold a10424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10418.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha10423.pow 1)))

@[irreducible]
def a10425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10419 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a10424 ^ 1)
theorem ha10425 : a10425.IsHomogeneous 104 := by
  unfold a10425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha10424.pow 1)))

@[irreducible]
def a10426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10425 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10422 ^ 1)
theorem ha10426 : a10426.IsHomogeneous 106 := by
  unfold a10426
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10422.pow 1)))

@[irreducible]
def a10427 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a03921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a07297 ^ 1)
theorem ha10427 : a10427.IsHomogeneous 100 := by
  unfold a10427
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha03921.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha07297.pow 1)))

@[irreducible]
def a10428 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a10420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10427 ^ 1)
theorem ha10428 : a10428.IsHomogeneous 106 := by
  unfold a10428
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha10420.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10427.pow 1)))

@[irreducible]
def a10429 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a10428 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10421 ^ 1)
theorem ha10429 : a10429.IsHomogeneous 106 := by
  unfold a10429
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha10428.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10421.pow 1)))

@[irreducible]
def a10430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10429 ^ 1)
theorem ha10430 : a10430.IsHomogeneous 106 := by
  unfold a10430
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10429.pow 1)))

@[irreducible]
def a10431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10430 ^ 1)
theorem ha10431 : a10431.IsHomogeneous 106 := by
  unfold a10431
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10430.pow 1)))

@[irreducible]
def a10432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10431 ^ 1) + (C ((81 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a10416 ^ 1)
theorem ha10432 : a10432.IsHomogeneous 106 := by
  unfold a10432
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10431.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha10416.pow 1)))

@[irreducible]
def a10433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01248 ^ 1 * a01702 ^ 1)
theorem ha10433 : a10433.IsHomogeneous 90 := by
  unfold a10433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02792.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01248.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a10434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01248 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00469 ^ 1 * a03562 ^ 1)
theorem ha10434 : a10434.IsHomogeneous 93 := by
  unfold a10434
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01248.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00469.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10434 ^ 1)
theorem ha10435 : a10435.IsHomogeneous 93 := by
  unfold a10435
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10434.pow 1)))

@[irreducible]
def a10436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02792 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a05526 ^ 1)
theorem ha10436 : a10436.IsHomogeneous 93 := by
  unfold a10436
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha05526.pow 1)))

@[irreducible]
def a10437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10436 ^ 1)
theorem ha10437 : a10437.IsHomogeneous 93 := by
  unfold a10437
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10436.pow 1)))

@[irreducible]
def a10438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10437 ^ 1)
theorem ha10438 : a10438.IsHomogeneous 93 := by
  unfold a10438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10437.pow 1)))

@[irreducible]
def a10439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00141 ^ 1 * a06725 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00469 ^ 1 * a03562 ^ 1)
theorem ha10439 : a10439.IsHomogeneous 87 := by
  unfold a10439
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00141.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00469.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10434 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10439 ^ 1)
theorem ha10440 : a10440.IsHomogeneous 93 := by
  unfold a10440
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10434.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10439.pow 1)))

@[irreducible]
def a10441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10435 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10440 ^ 1)
theorem ha10441 : a10441.IsHomogeneous 93 := by
  unfold a10441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10435.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10440.pow 1)))

@[irreducible]
def a10442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10438 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10441 ^ 1)
theorem ha10442 : a10442.IsHomogeneous 93 := by
  unfold a10442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10438.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10441.pow 1)))

@[irreducible]
def a10443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10395 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a10410 ^ 1)
theorem ha10443 : a10443.IsHomogeneous 42 := by
  unfold a10443
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10395.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha10410.pow 1)))

@[irreducible]
def a10444 : Poly := (C ((-15 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a05526 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10443 ^ 1)
theorem ha10444 : a10444.IsHomogeneous 87 := by
  unfold a10444
  exact ((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha05526.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10443.pow 1)))

@[irreducible]
def a10445 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10444 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10436 ^ 1)
theorem ha10445 : a10445.IsHomogeneous 93 := by
  unfold a10445
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10436.pow 1)))

@[irreducible]
def a10446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10437 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10445 ^ 1)
theorem ha10446 : a10446.IsHomogeneous 93 := by
  unfold a10446
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10437.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10445.pow 1)))

@[irreducible]
def a10447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10438 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10446 ^ 1)
theorem ha10447 : a10447.IsHomogeneous 93 := by
  unfold a10447
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10438.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10446.pow 1)))

@[irreducible]
def a10448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10442 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10447 ^ 1)
theorem ha10448 : a10448.IsHomogeneous 93 := by
  unfold a10448
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10447.pow 1)))

@[irreducible]
def a10449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10431 ^ 1) + (C ((54 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a10448 ^ 1)
theorem ha10449 : a10449.IsHomogeneous 106 := by
  unfold a10449
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10431.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha10448.pow 1)))

@[irreducible]
def a10450 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a10449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10432 ^ 1)
theorem ha10450 : a10450.IsHomogeneous 106 := by
  unfold a10450
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha10449.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10432.pow 1)))

@[irreducible]
def a10451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01253 ^ 1 * a01702 ^ 1)
theorem ha10451 : a10451.IsHomogeneous 90 := by
  unfold a10451
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02799.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01253.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a10452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01253 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00473 ^ 1 * a03562 ^ 1)
theorem ha10452 : a10452.IsHomogeneous 93 := by
  unfold a10452
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01253.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00473.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10452 ^ 1)
theorem ha10453 : a10453.IsHomogeneous 93 := by
  unfold a10453
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10452.pow 1)))

@[irreducible]
def a10454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02799 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a05536 ^ 1)
theorem ha10454 : a10454.IsHomogeneous 93 := by
  unfold a10454
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02799.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha05536.pow 1)))

@[irreducible]
def a10455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10454 ^ 1)
theorem ha10455 : a10455.IsHomogeneous 93 := by
  unfold a10455
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10454.pow 1)))

@[irreducible]
def a10456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10455 ^ 1)
theorem ha10456 : a10456.IsHomogeneous 93 := by
  unfold a10456
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10453.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10455.pow 1)))

@[irreducible]
def a10457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10410 ^ 1)
theorem ha10457 : a10457.IsHomogeneous 42 := by
  unfold a10457
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10395.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10410.pow 1)))

@[irreducible]
def a10458 : Poly := (C ((-15 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a05536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a10457 ^ 1)
theorem ha10458 : a10458.IsHomogeneous 87 := by
  unfold a10458
  exact ((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha05536.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10457.pow 1)))

@[irreducible]
def a10459 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10454 ^ 1)
theorem ha10459 : a10459.IsHomogeneous 93 := by
  unfold a10459
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10454.pow 1)))

@[irreducible]
def a10460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10459 ^ 1)
theorem ha10460 : a10460.IsHomogeneous 93 := by
  unfold a10460
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10459.pow 1)))

@[irreducible]
def a10461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10460 ^ 1)
theorem ha10461 : a10461.IsHomogeneous 93 := by
  unfold a10461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10460.pow 1)))

@[irreducible]
def a10462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00144 ^ 1 * a06725 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00473 ^ 1 * a03562 ^ 1)
theorem ha10462 : a10462.IsHomogeneous 87 := by
  unfold a10462
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00144.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00473.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10452 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10462 ^ 1)
theorem ha10463 : a10463.IsHomogeneous 93 := by
  unfold a10463
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10452.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10462.pow 1)))

@[irreducible]
def a10464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10463 ^ 1)
theorem ha10464 : a10464.IsHomogeneous 93 := by
  unfold a10464
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10453.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10463.pow 1)))

@[irreducible]
def a10465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10456 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10464 ^ 1)
theorem ha10465 : a10465.IsHomogeneous 93 := by
  unfold a10465
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10464.pow 1)))

@[irreducible]
def a10466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10465 ^ 1)
theorem ha10466 : a10466.IsHomogeneous 93 := by
  unfold a10466
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10465.pow 1)))

@[irreducible]
def a10467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10431 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a10466 ^ 1)
theorem ha10467 : a10467.IsHomogeneous 106 := by
  unfold a10467
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10431.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha10466.pow 1)))

@[irreducible]
def a10468 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a10467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10450 ^ 1)
theorem ha10468 : a10468.IsHomogeneous 106 := by
  unfold a10468
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha10467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10450.pow 1)))

@[irreducible]
def a10469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00299 ^ 1 * a05545 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a10468 ^ 1)
theorem ha10469 : a10469.IsHomogeneous 124 := by
  unfold a10469
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00299.pow 1)).mul (ha05545.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha10468.pow 1)))

@[irreducible]
def a10470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a10364 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10469 ^ 1)
theorem ha10470 : a10470.IsHomogeneous 124 := by
  unfold a10470
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha10364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10469.pow 1)))

@[irreducible]
def a10471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10365 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10470 ^ 1)
theorem ha10471 : a10471.IsHomogeneous 124 := by
  unfold a10471
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10365.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10470.pow 1)))

@[irreducible]
def a10472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10366 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a10471 ^ 1)
theorem ha10472 : a10472.IsHomogeneous 124 := by
  unfold a10472
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10366.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha10471.pow 1)))

@[irreducible]
def a10473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10472 ^ 1)
theorem ha10473 : a10473.IsHomogeneous 124 := by
  unfold a10473
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10370.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10472.pow 1)))

@[irreducible]
def a10474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a10473 ^ 1) + (C ((108 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a10360 ^ 1)
theorem ha10474 : a10474.IsHomogeneous 130 := by
  unfold a10474
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha10473.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha10360.pow 1)))

@[irreducible]
def a10475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a05550 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a10474 ^ 1)
theorem ha10475 : a10475.IsHomogeneous 136 := by
  unfold a10475
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha05550.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha10474.pow 1)))

@[irreducible]
def a10476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a10340 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a10475 ^ 1)
theorem ha10476 : a10476.IsHomogeneous 142 := by
  unfold a10476
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha10340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha10475.pow 1)))

@[irreducible]
def a10477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10341 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a10476 ^ 1)
theorem ha10477 : a10477.IsHomogeneous 148 := by
  unfold a10477
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10341.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha10476.pow 1)))

@[irreducible]
def a10478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10477 ^ 1)
theorem ha10478 : a10478.IsHomogeneous 148 := by
  unfold a10478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10342.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10477.pow 1)))

@[irreducible]
def a10479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a10346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10478 ^ 1)
theorem ha10479 : a10479.IsHomogeneous 148 := by
  unfold a10479
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha10346.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10478.pow 1)))

@[irreducible]
def a10480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a10479 ^ 1) + (C ((729 : ℂ) / (1000 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a10336 ^ 1)
theorem ha10480 : a10480.IsHomogeneous 160 := by
  unfold a10480
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha10479.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (1000 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha10336.pow 1)))

@[irreducible]
def a10481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00126 ^ 1 * a10480 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a05555 ^ 1)
theorem ha10481 : a10481.IsHomogeneous 191 := by
  unfold a10481
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00126.pow 1)).mul (ha10480.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha05555.pow 1)))

@[irreducible]
def a10482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10481 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10250 ^ 1)
theorem ha10482 : a10482.IsHomogeneous 191 := by
  unfold a10482
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10481.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10250.pow 1)))

@[irreducible]
def a10483 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10482 ^ 1)
theorem ha10483 : a10483.IsHomogeneous 191 := by
  unfold a10483
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10482.pow 1)))

@[irreducible]
def a10484 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10483 ^ 1)
theorem ha10484 : a10484.IsHomogeneous 191 := by
  unfold a10484
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10483.pow 1)))

@[irreducible]
def a10485 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a10256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10484 ^ 1)
theorem ha10485 : a10485.IsHomogeneous 191 := by
  unfold a10485
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha10256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10484.pow 1)))

@[irreducible]
def a10486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10485 ^ 1) + (C ((27 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a10246 ^ 1)
theorem ha10486 : a10486.IsHomogeneous 191 := by
  unfold a10486
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10485.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha10246.pow 1)))

@[irreducible]
def a10487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01284 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02851 ^ 1)
theorem ha10487 : a10487.IsHomogeneous 427 := by
  unfold a10487
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01284.pow 1)).mul (ha01949.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a10488 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01284 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a03978 ^ 1)
theorem ha10488 : a10488.IsHomogeneous 451 := by
  unfold a10488
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01284.pow 1)).mul (ha01949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a10489 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a10487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10488 ^ 1)
theorem ha10489 : a10489.IsHomogeneous 451 := by
  unfold a10489
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha10487.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10488.pow 1)))

@[irreducible]
def a10490 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a05615 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a02851 ^ 1)
theorem ha10490 : a10490.IsHomogeneous 367 := by
  unfold a10490
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha05615.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a10491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10487 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10490 ^ 1)
theorem ha10491 : a10491.IsHomogeneous 427 := by
  unfold a10491
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10487.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10490.pow 1)))

@[irreducible]
def a10492 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a10491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10489 ^ 1)
theorem ha10492 : a10492.IsHomogeneous 451 := by
  unfold a10492
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha10491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10489.pow 1)))

@[irreducible]
def a10493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00831 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a01941 ^ 1)
theorem ha10493 : a10493.IsHomogeneous 132 := by
  unfold a10493
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00831.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a10494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01941 ^ 1)
theorem ha10494 : a10494.IsHomogeneous 132 := by
  unfold a10494
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03967.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a10495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10493 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a10494 ^ 1)
theorem ha10495 : a10495.IsHomogeneous 132 := by
  unfold a10495
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha10494.pow 1)))

end CycleQ2Concrete
