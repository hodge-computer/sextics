import Proposal.CurrentAtoms024

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a08192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08184 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08191 ^ 1)
theorem ha08192 : a08192.IsHomogeneous 30 := by
  unfold a08192
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08184.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08191.pow 1)))

@[irreducible]
def a08193 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08192 ^ 1)
theorem ha08193 : a08193.IsHomogeneous 36 := by
  unfold a08193
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08192.pow 1)))

@[irreducible]
def a08194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08175 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08193 ^ 1)
theorem ha08194 : a08194.IsHomogeneous 36 := by
  unfold a08194
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08193.pow 1)))

@[irreducible]
def a08195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a07875 ^ 1 * a08194 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a07904 ^ 1 * a08146 ^ 1)
theorem ha08195 : a08195.IsHomogeneous 165 := by
  unfold a08195
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha07875.pow 1)).mul (ha08194.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha07904.pow 1)).mul (ha08146.pow 1)))

@[irreducible]
def a08196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08138 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a08144 ^ 1)
theorem ha08196 : a08196.IsHomogeneous 49 := by
  unfold a08196
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha08144.pow 1)))

@[irreducible]
def a08197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08142 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07874 ^ 1 * a08140 ^ 1)
theorem ha08197 : a08197.IsHomogeneous 92 := by
  unfold a08197
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08142.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07874.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a08196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08197 ^ 1)
theorem ha08198 : a08198.IsHomogeneous 92 := by
  unfold a08198
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha08196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08197.pow 1)))

@[irreducible]
def a08199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07887 ^ 1 * a08148 ^ 1)
theorem ha08199 : a08199.IsHomogeneous 24 := by
  unfold a08199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08162.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07887.pow 1)).mul (ha08148.pow 1)))

@[irreducible]
def a08200 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07883 ^ 1 * a08147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08156 ^ 1)
theorem ha08200 : a08200.IsHomogeneous 25 := by
  unfold a08200
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07883.pow 1)).mul (ha08147.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08156.pow 1)))

@[irreducible]
def a08201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08200 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08199 ^ 1)
theorem ha08201 : a08201.IsHomogeneous 31 := by
  unfold a08201
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08200.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08199.pow 1)))

@[irreducible]
def a08202 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a08167 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07879 ^ 1 * a08168 ^ 1)
theorem ha08202 : a08202.IsHomogeneous 25 := by
  unfold a08202
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha08167.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07879.pow 1)).mul (ha08168.pow 1)))

@[irreducible]
def a08203 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07890 ^ 1 * a08172 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07884 ^ 1 * a08170 ^ 1)
theorem ha08203 : a08203.IsHomogeneous 24 := by
  unfold a08203
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07890.pow 1)).mul (ha08172.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07884.pow 1)).mul (ha08170.pow 1)))

@[irreducible]
def a08204 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08202 ^ 1)
theorem ha08204 : a08204.IsHomogeneous 31 := by
  unfold a08204
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08203.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08202.pow 1)))

@[irreducible]
def a08205 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08204 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08201 ^ 1)
theorem ha08205 : a08205.IsHomogeneous 31 := by
  unfold a08205
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08204.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08201.pow 1)))

@[irreducible]
def a08206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07897 ^ 1 * a08148 ^ 1)
theorem ha08206 : a08206.IsHomogeneous 24 := by
  unfold a08206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08182.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07897.pow 1)).mul (ha08148.pow 1)))

@[irreducible]
def a08207 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07868 ^ 1 * a07894 ^ 1 * a08147 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a07877 ^ 1 * a07889 ^ 1 * a07894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07877 ^ 1 * a08177 ^ 1)
theorem ha08207 : a08207.IsHomogeneous 25 := by
  unfold a08207
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07868.pow 1)).mul (ha07894.pow 1)).mul (ha08147.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07877.pow 1)).mul (ha07889.pow 1)).mul (ha07894.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07877.pow 1)).mul (ha08177.pow 1)))

@[irreducible]
def a08208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08207 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08206 ^ 1)
theorem ha08208 : a08208.IsHomogeneous 31 := by
  unfold a08208
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08207.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08206.pow 1)))

@[irreducible]
def a08209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07899 ^ 1 * a08189 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07901 ^ 1 * a08186 ^ 1)
theorem ha08209 : a08209.IsHomogeneous 25 := by
  unfold a08209
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07899.pow 1)).mul (ha08189.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07901.pow 1)).mul (ha08186.pow 1)))

@[irreducible]
def a08210 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07889 ^ 1 * a07900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07900 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07868 ^ 1 * a08188 ^ 1)
theorem ha08210 : a08210.IsHomogeneous 24 := by
  unfold a08210
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07889.pow 1)).mul (ha07900.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07900.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07868.pow 1)).mul (ha08188.pow 1)))

@[irreducible]
def a08211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08209 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08210 ^ 1)
theorem ha08211 : a08211.IsHomogeneous 31 := by
  unfold a08211
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08209.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08210.pow 1)))

@[irreducible]
def a08212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08208 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08211 ^ 1)
theorem ha08212 : a08212.IsHomogeneous 31 := by
  unfold a08212
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08208.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08211.pow 1)))

@[irreducible]
def a08213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08205 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a08212 ^ 1)
theorem ha08213 : a08213.IsHomogeneous 31 := by
  unfold a08213
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha08212.pow 1)))

@[irreducible]
def a08214 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a07889 ^ 1 * a07905 ^ 1 * a07912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07873 ^ 1 * a07905 ^ 1 * a08213 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07912 ^ 1 * a08198 ^ 1)
theorem ha08214 : a08214.IsHomogeneous 129 := by
  unfold a08214
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha07889.pow 1)).mul (ha07905.pow 1)).mul (ha07912.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07873.pow 1)).mul (ha07905.pow 1)).mul (ha08213.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07912.pow 1)).mul (ha08198.pow 1)))

@[irreducible]
def a08215 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 3 * a00025 ^ 1 * a08214 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08195 ^ 1)
theorem ha08215 : a08215.IsHomogeneous 165 := by
  unfold a08215
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).mul (ha08214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08195.pow 1)))

@[irreducible]
def a08216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07870 ^ 1 * a07889 ^ 1)
theorem ha08216 : a08216.IsHomogeneous 36 := by
  unfold a08216
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07870.pow 1)).mul (ha07889.pow 1)))

@[irreducible]
def a08217 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a07873 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a08216 ^ 1)
theorem ha08217 : a08217.IsHomogeneous 66 := by
  unfold a08217
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha07873.pow 1)).mul (ha08140.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha08216.pow 1)))

@[irreducible]
def a08218 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a07889 ^ 1)
theorem ha08218 : a08218.IsHomogeneous 18 := by
  unfold a08218
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha07889.pow 1)))

@[irreducible]
def a08219 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08218 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07915 ^ 1)
theorem ha08219 : a08219.IsHomogeneous 18 := by
  unfold a08219
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08218.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07915.pow 1)))

@[irreducible]
def a08220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a08139 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08219 ^ 1)
theorem ha08220 : a08220.IsHomogeneous 18 := by
  unfold a08220
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha08139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08219.pow 1)))

@[irreducible]
def a08221 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07916 ^ 1 * a08217 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07914 ^ 1 * a08220 ^ 1)
theorem ha08221 : a08221.IsHomogeneous 84 := by
  unfold a08221
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07916.pow 1)).mul (ha08217.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07914.pow 1)).mul (ha08220.pow 1)))

@[irreducible]
def a08222 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a07873 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a08140 ^ 1)
theorem ha08222 : a08222.IsHomogeneous 36 := by
  unfold a08222
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha07873.pow 1)).mul (ha08135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08223 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3) + (C ((1 : ℂ) / (1 : ℂ)) * a08218 ^ 1)
theorem ha08223 : a08223.IsHomogeneous 18 := by
  unfold a08223
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08218.pow 1)))

@[irreducible]
def a08224 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07917 ^ 1 * a08222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07870 ^ 1 * a07873 ^ 1 * a08223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a07873 ^ 1 * a07889 ^ 1 * a07917 ^ 1)
theorem ha08224 : a08224.IsHomogeneous 60 := by
  unfold a08224
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07917.pow 1)).mul (ha08222.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07870.pow 1)).mul (ha07873.pow 1)).mul (ha08223.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha07873.pow 1)).mul (ha07889.pow 1)).mul (ha07917.pow 1)))

@[irreducible]
def a08225 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08221 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00014 ^ 3 * a08224 ^ 1)
theorem ha08225 : a08225.IsHomogeneous 84 := by
  unfold a08225
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08221.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha08224.pow 1)))

@[irreducible]
def a08226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a07871 ^ 1 * a08137 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a08136 ^ 1)
theorem ha08226 : a08226.IsHomogeneous 43 := by
  unfold a08226
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha07871.pow 1)).mul (ha08137.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha08136.pow 1)))

@[irreducible]
def a08227 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07871 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08137 ^ 1)
theorem ha08227 : a08227.IsHomogeneous 25 := by
  unfold a08227
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07871.pow 1)).mul (ha07889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08137.pow 1)))

@[irreducible]
def a08228 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 2 * a08227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08226 ^ 1)
theorem ha08228 : a08228.IsHomogeneous 49 := by
  unfold a08228
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 2)).mul (ha08227.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08226.pow 1)))

@[irreducible]
def a08229 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00017 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha08229 : a08229.IsHomogeneous 19 := by
  unfold a08229
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00017.pow 1)).mul (ha07889.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a08230 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a08229 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a07889 ^ 1)
theorem ha08230 : a08230.IsHomogeneous 30 := by
  unfold a08230
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha08229.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha07889.pow 1)))

@[irreducible]
def a08231 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07922 ^ 1 * a08228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07920 ^ 1 * a08230 ^ 1)
theorem ha08231 : a08231.IsHomogeneous 79 := by
  unfold a08231
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07922.pow 1)).mul (ha08228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07920.pow 1)).mul (ha08230.pow 1)))

@[irreducible]
def a08232 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07873 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08140 ^ 1)
theorem ha08232 : a08232.IsHomogeneous 12 := by
  unfold a08232
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha07889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07873.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08231 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00009 ^ 1 * a00014 ^ 6 * a00025 ^ 1 * a08232 ^ 1)
theorem ha08233 : a08233.IsHomogeneous 79 := by
  unfold a08233
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08231.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 6)).mul (ha00025.pow 1)).mul (ha08232.pow 1)))

@[irreducible]
def a08234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 1 * a08137 ^ 1)
theorem ha08234 : a08234.IsHomogeneous 36 := by
  unfold a08234
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08135.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha08137.pow 1)))

@[irreducible]
def a08235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07870 ^ 1 * a08234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07924 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a07889 ^ 1 * a07924 ^ 1)
theorem ha08235 : a08235.IsHomogeneous 72 := by
  unfold a08235
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07870.pow 1)).mul (ha08234.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07924.pow 1)).mul (ha08135.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha07889.pow 1)).mul (ha07924.pow 1)))

@[irreducible]
def a08236 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00009 ^ 1 * a00014 ^ 6 * a07873 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08235 ^ 1)
theorem ha08236 : a08236.IsHomogeneous 72 := by
  unfold a08236
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 6)).mul (ha07873.pow 1)).mul (ha08140.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08235.pow 1)))

@[irreducible]
def a08237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08233 ^ 1) + (C ((54 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a08236 ^ 1)
theorem ha08237 : a08237.IsHomogeneous 79 := by
  unfold a08237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08233.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha08236.pow 1)))

@[irreducible]
def a08238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00025 ^ 2 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08137 ^ 1)
theorem ha08238 : a08238.IsHomogeneous 25 := by
  unfold a08238
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00025.pow 2)).mul (ha07889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08137.pow 1)))

@[irreducible]
def a08239 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07927 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a08238 ^ 1)
theorem ha08239 : a08239.IsHomogeneous 55 := by
  unfold a08239
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07927.pow 1)).mul (ha08135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha08238.pow 1)))

@[irreducible]
def a08240 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a07889 ^ 1 * a07927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08239 ^ 1)
theorem ha08240 : a08240.IsHomogeneous 61 := by
  unfold a08240
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha07889.pow 1)).mul (ha07927.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08239.pow 1)))

@[irreducible]
def a08241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a08240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08237 ^ 1)
theorem ha08241 : a08241.IsHomogeneous 79 := by
  unfold a08241
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha08240.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08237.pow 1)))

@[irreducible]
def a08242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a08241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07928 ^ 1 * a08168 ^ 1)
theorem ha08242 : a08242.IsHomogeneous 85 := by
  unfold a08242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha08241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07928.pow 1)).mul (ha08168.pow 1)))

@[irreducible]
def a08243 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a07895 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08179 ^ 1)
theorem ha08243 : a08243.IsHomogeneous 12 := by
  unfold a08243
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha07895.pow 1)).mul (ha08140.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08179.pow 1)))

@[irreducible]
def a08244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00025 ^ 1 * a08243 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00000 ^ 3 * a00002 ^ 1 * a00003 ^ 2 * a08228 ^ 1)
theorem ha08244 : a08244.IsHomogeneous 55 := by
  unfold a08244
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).mul (ha08243.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha08228.pow 1)))

@[irreducible]
def a08245 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08244 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a08239 ^ 1)
theorem ha08245 : a08245.IsHomogeneous 57 := by
  unfold a08245
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08244.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha08239.pow 1)))

@[irreducible]
def a08246 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08245 ^ 1)
theorem ha08246 : a08246.IsHomogeneous 63 := by
  unfold a08246
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07930.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07930.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08245.pow 1)))

@[irreducible]
def a08247 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08246 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08242 ^ 1)
theorem ha08247 : a08247.IsHomogeneous 85 := by
  unfold a08247
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08246.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08242.pow 1)))

@[irreducible]
def a08248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07918 ^ 1 * a08247 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07931 ^ 1 * a08225 ^ 1)
theorem ha08248 : a08248.IsHomogeneous 169 := by
  unfold a08248
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07918.pow 1)).mul (ha08247.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07931.pow 1)).mul (ha08225.pow 1)))

@[irreducible]
def a08249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07914 ^ 1 * a08223 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07917 ^ 1 * a08217 ^ 1)
theorem ha08249 : a08249.IsHomogeneous 84 := by
  unfold a08249
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07914.pow 1)).mul (ha08223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07917.pow 1)).mul (ha08217.pow 1)))

@[irreducible]
def a08250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a07873 ^ 1 * a08220 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07916 ^ 1 * a08222 ^ 1)
theorem ha08250 : a08250.IsHomogeneous 54 := by
  unfold a08250
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha07873.pow 1)).mul (ha08220.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07916.pow 1)).mul (ha08222.pow 1)))

@[irreducible]
def a08251 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 3 * a08250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08249 ^ 1)
theorem ha08251 : a08251.IsHomogeneous 90 := by
  unfold a08251
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 3)).mul (ha08250.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08249.pow 1)))

@[irreducible]
def a08252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07920 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08228 ^ 1)
theorem ha08252 : a08252.IsHomogeneous 49 := by
  unfold a08252
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08228.pow 1)))

@[irreducible]
def a08253 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a07922 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08230 ^ 1)
theorem ha08253 : a08253.IsHomogeneous 36 := by
  unfold a08253
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha07922.pow 1)).mul (ha08140.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08230.pow 1)))

@[irreducible]
def a08254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08252 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a08253 ^ 1)
theorem ha08254 : a08254.IsHomogeneous 49 := by
  unfold a08254
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08252.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha08253.pow 1)))

@[irreducible]
def a08255 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a07924 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08234 ^ 1)
theorem ha08255 : a08255.IsHomogeneous 42 := by
  unfold a08255
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha07924.pow 1)).mul (ha08140.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08234.pow 1)))

@[irreducible]
def a08256 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a08255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08222 ^ 1)
theorem ha08256 : a08256.IsHomogeneous 42 := by
  unfold a08256
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha08255.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08222.pow 1)))

@[irreducible]
def a08257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08254 ^ 1) + (C ((81 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a08256 ^ 1)
theorem ha08257 : a08257.IsHomogeneous 49 := by
  unfold a08257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08254.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha08256.pow 1)))

@[irreducible]
def a08258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a08238 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07927 ^ 1 * a08140 ^ 1)
theorem ha08258 : a08258.IsHomogeneous 31 := by
  unfold a08258
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha08238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07927.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08259 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a08258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08257 ^ 1)
theorem ha08259 : a08259.IsHomogeneous 49 := by
  unfold a08259
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha08258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08257.pow 1)))

@[irreducible]
def a08260 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07936 ^ 1 * a08168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a08259 ^ 1)
theorem ha08260 : a08260.IsHomogeneous 55 := by
  unfold a08260
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07936.pow 1)).mul (ha08168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha08259.pow 1)))

@[irreducible]
def a08261 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07920 ^ 1 * a08179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07895 ^ 1 * a08228 ^ 1)
theorem ha08261 : a08261.IsHomogeneous 55 := by
  unfold a08261
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07920.pow 1)).mul (ha08179.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07895.pow 1)).mul (ha08228.pow 1)))

@[irreducible]
def a08262 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a07873 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08140 ^ 1)
theorem ha08262 : a08262.IsHomogeneous 12 := by
  unfold a08262
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha07873.pow 1)).mul (ha07889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08263 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1 * a08262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08261 ^ 1)
theorem ha08263 : a08263.IsHomogeneous 55 := by
  unfold a08263
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha08262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08261.pow 1)))

@[irreducible]
def a08264 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08263 ^ 1)
theorem ha08264 : a08264.IsHomogeneous 55 := by
  unfold a08264
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08263.pow 1)))

@[irreducible]
def a08265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07938 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08264 ^ 1)
theorem ha08265 : a08265.IsHomogeneous 55 := by
  unfold a08265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08264.pow 1)))

@[irreducible]
def a08266 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08265 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08260 ^ 1)
theorem ha08266 : a08266.IsHomogeneous 55 := by
  unfold a08266
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08260.pow 1)))

@[irreducible]
def a08267 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07939 ^ 1 * a08251 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07932 ^ 1 * a07939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07932 ^ 1 * a08266 ^ 1)
theorem ha08267 : a08267.IsHomogeneous 151 := by
  unfold a08267
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07939.pow 1)).mul (ha08251.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07932.pow 1)).mul (ha07939.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07932.pow 1)).mul (ha08266.pow 1)))

@[irreducible]
def a08268 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a08267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08248 ^ 1)
theorem ha08268 : a08268.IsHomogeneous 169 := by
  unfold a08268
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha08267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08248.pow 1)))

@[irreducible]
def a08269 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07939 ^ 1 * a08225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07918 ^ 1 * a08266 ^ 1)
theorem ha08269 : a08269.IsHomogeneous 139 := by
  unfold a08269
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07939.pow 1)).mul (ha08225.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07918.pow 1)).mul (ha08266.pow 1)))

@[irreducible]
def a08270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07931 ^ 1 * a08251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07932 ^ 1 * a08247 ^ 1)
theorem ha08270 : a08270.IsHomogeneous 175 := by
  unfold a08270
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07931.pow 1)).mul (ha08251.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07932.pow 1)).mul (ha08247.pow 1)))

@[irreducible]
def a08271 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 3 * a08269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08270 ^ 1)
theorem ha08271 : a08271.IsHomogeneous 175 := by
  unfold a08271
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 3)).mul (ha08269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08270.pow 1)))

@[irreducible]
def a08272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08271 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07889 ^ 1 * a07941 ^ 1)
theorem ha08272 : a08272.IsHomogeneous 181 := by
  unfold a08272
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08271.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07889.pow 1)).mul (ha07941.pow 1)))

@[irreducible]
def a08273 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a07940 ^ 1 * a08268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07941 ^ 1 * a08272 ^ 1)
theorem ha08273 : a08273.IsHomogeneous 356 := by
  unfold a08273
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha07940.pow 1)).mul (ha08268.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07941.pow 1)).mul (ha08272.pow 1)))

@[irreducible]
def a08274 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07942 ^ 1 * a08268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07940 ^ 1 * a08273 ^ 1)
theorem ha08274 : a08274.IsHomogeneous 525 := by
  unfold a08274
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07942.pow 1)).mul (ha08268.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07940.pow 1)).mul (ha08273.pow 1)))

@[irreducible]
def a08275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07913 ^ 1 * a08274 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07940 ^ 1 * a07942 ^ 1 * a08215 ^ 1)
theorem ha08275 : a08275.IsHomogeneous 690 := by
  unfold a08275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07913.pow 1)).mul (ha08274.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07940.pow 1)).mul (ha07942.pow 1)).mul (ha08215.pow 1)))

@[irreducible]
def a08276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a07875 ^ 1 * a08213 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a07912 ^ 1 * a08146 ^ 1)
theorem ha08276 : a08276.IsHomogeneous 160 := by
  unfold a08276
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha07875.pow 1)).mul (ha08213.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha07912.pow 1)).mul (ha08146.pow 1)))

@[irreducible]
def a08277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07873 ^ 1 * a07905 ^ 1 * a08194 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07904 ^ 1 * a08198 ^ 1)
theorem ha08277 : a08277.IsHomogeneous 128 := by
  unfold a08277
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07873.pow 1)).mul (ha07905.pow 1)).mul (ha08194.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07904.pow 1)).mul (ha08198.pow 1)))

@[irreducible]
def a08278 : Poly := (C ((-1296 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00025 ^ 1 * a08277 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08276 ^ 1)
theorem ha08278 : a08278.IsHomogeneous 160 := by
  unfold a08278
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1296 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).mul (ha08277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08276.pow 1)))

@[irreducible]
def a08279 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07942 ^ 1 * a08271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07941 ^ 1 * a08273 ^ 1)
theorem ha08279 : a08279.IsHomogeneous 531 := by
  unfold a08279
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07942.pow 1)).mul (ha08271.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07941.pow 1)).mul (ha08273.pow 1)))

@[irreducible]
def a08280 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07941 ^ 1 * a07942 ^ 1 * a07943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07941 ^ 1 * a07942 ^ 1 * a08278 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07943 ^ 1 * a08279 ^ 1)
theorem ha08280 : a08280.IsHomogeneous 697 := by
  unfold a08280
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07941.pow 1)).mul (ha07942.pow 1)).mul (ha07943.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07941.pow 1)).mul (ha07942.pow 1)).mul (ha08278.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07943.pow 1)).mul (ha08279.pow 1)))

@[irreducible]
def a08281 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08280 ^ 1)
theorem ha08281 : a08281.IsHomogeneous 697 := by
  unfold a08281
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08275.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08280.pow 1)))

@[irreducible]
def a08282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07913 ^ 1 * a08279 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07941 ^ 1 * a07942 ^ 1 * a08215 ^ 1)
theorem ha08282 : a08282.IsHomogeneous 696 := by
  unfold a08282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07913.pow 1)).mul (ha08279.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07941.pow 1)).mul (ha07942.pow 1)).mul (ha08215.pow 1)))

@[irreducible]
def a08283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07940 ^ 1 * a07942 ^ 1 * a08278 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07943 ^ 1 * a08274 ^ 1)
theorem ha08283 : a08283.IsHomogeneous 685 := by
  unfold a08283
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07940.pow 1)).mul (ha07942.pow 1)).mul (ha08278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07943.pow 1)).mul (ha08274.pow 1)))

@[irreducible]
def a08284 : Poly := (C ((-1 : ℂ) / (648 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08282 ^ 1)
theorem ha08284 : a08284.IsHomogeneous 696 := by
  unfold a08284
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08282.pow 1)))

@[irreducible]
def a08285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a08281 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a08284 ^ 1)
theorem ha08285 : a08285.IsHomogeneous 698 := by
  unfold a08285
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha08281.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha08284.pow 1)))

@[irreducible]
def a08286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07947 ^ 1 * a08285 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00005 ^ 1 * a07942 ^ 1 * a07946 ^ 1 * a07993 ^ 1)
theorem ha08286 : a08286.IsHomogeneous 704 := by
  unfold a08286
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07947.pow 1)).mul (ha08285.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00005.pow 1)).mul (ha07942.pow 1)).mul (ha07946.pow 1)).mul (ha07993.pow 1)))

@[irreducible]
def a08287 : Poly := (C ((-46656 : ℂ) / (1 : ℂ)) * a00002 ^ 2 * a00005 ^ 2 * a00105 ^ 1 * a07942 ^ 2 * a07947 ^ 2 * a08133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 2 * a00012 ^ 1 * a00013 ^ 2 * a00014 ^ 6 * a00103 ^ 4 * a00106 ^ 3 * a00123 ^ 2 * a00124 ^ 2 * a07867 ^ 2 * a08286 ^ 1)
theorem ha08287 : a08287.IsHomogeneous 1502 := by
  unfold a08287
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-46656 : ℂ) / (1 : ℂ))).mul (ha00002.pow 2)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07942.pow 2)).mul (ha07947.pow 2)).mul (ha08133.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 2)).mul (ha00012.pow 1)).mul (ha00013.pow 2)).mul (ha00014.pow 6)).mul (ha00103.pow 4)).mul (ha00106.pow 3)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha07867.pow 2)).mul (ha08286.pow 1)))

@[irreducible]
def a08288 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00018 ^ 1 * a00031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00027 ^ 1 * a07970 ^ 1)
theorem ha08288 : a08288.IsHomogeneous 50 := by
  unfold a08288
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00018.pow 1)).mul (ha00031.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00027.pow 1)).mul (ha07970.pow 1)))

@[irreducible]
def a08289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07945 ^ 1 * a07947 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00001 ^ 1 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a07946 ^ 1)
theorem ha08289 : a08289.IsHomogeneous 346 := by
  unfold a08289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07945.pow 1)).mul (ha07947.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07946.pow 1)))

@[irreducible]
def a08290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 2 * a00005 ^ 2 * a00105 ^ 2 * a07864 ^ 1 * a07942 ^ 1 * a07947 ^ 2) + (C ((1 : ℂ) / (432 : ℂ)) * a00001 ^ 2 * a00004 ^ 2 * a00013 ^ 2 * a00014 ^ 6 * a00103 ^ 3 * a00106 ^ 2 * a00123 ^ 1 * a00124 ^ 1 * a07867 ^ 1 * a08289 ^ 1)
theorem ha08290 : a08290.IsHomogeneous 820 := by
  unfold a08290
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 2)).mul (ha00005.pow 2)).mul (ha00105.pow 2)).mul (ha07864.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 2)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 2)).mul (ha00004.pow 2)).mul (ha00013.pow 2)).mul (ha00014.pow 6)).mul (ha00103.pow 3)).mul (ha00106.pow 2)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07867.pow 1)).mul (ha08289.pow 1)))

@[irreducible]
def a08291 : Poly := (C ((-15552 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00103 ^ 1 * a00106 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a08288 ^ 1 * a08290 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00033 ^ 1 * a08287 ^ 1)
theorem ha08291 : a08291.IsHomogeneous 1565 := by
  unfold a08291
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-15552 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha08288.pow 1)).mul (ha08290.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00033.pow 1)).mul (ha08287.pow 1)))

@[irreducible]
def a08292 : Poly := (C ((-1 : ℂ) / (279936 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00013 ^ 1 * a00014 ^ 2 * a00018 ^ 2 * a00101 ^ 2 * a08291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 2 * a00106 ^ 2 * a00123 ^ 2 * a00124 ^ 1 * a07867 ^ 2 * a07942 ^ 2 * a08009 ^ 1)
theorem ha08292 : a08292.IsHomogeneous 1795 := by
  unfold a08292
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (279936 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 2)).mul (ha00018.pow 2)).mul (ha00101.pow 2)).mul (ha08291.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 2)).mul (ha00106.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 1)).mul (ha07867.pow 2)).mul (ha07942.pow 2)).mul (ha08009.pow 1)))

@[irreducible]
def a08293 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a04339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a02121 ^ 1)
theorem ha08293 : a08293.IsHomogeneous 732 := by
  unfold a08293
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha04339.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha02121.pow 1)))

@[irreducible]
def a08294 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01103 ^ 1)
theorem ha08294 : a08294.IsHomogeneous 799 := by
  unfold a08294
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08295 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00940 ^ 1 * a01118 ^ 1)
theorem ha08295 : a08295.IsHomogeneous 715 := by
  unfold a08295
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00940.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a08296 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00988 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02308 ^ 1)
theorem ha08296 : a08296.IsHomogeneous 856 := by
  unfold a08296
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00988.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08297 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00996 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a02327 ^ 1)
theorem ha08297 : a08297.IsHomogeneous 748 := by
  unfold a08297
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00996.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a08298 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a04445 ^ 1)
theorem ha08298 : a08298.IsHomogeneous 920 := by
  unfold a08298
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02173.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha04445.pow 1)))

@[irreducible]
def a08299 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a04468 ^ 1)
theorem ha08299 : a08299.IsHomogeneous 788 := by
  unfold a08299
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha02183.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha04468.pow 1)))

@[irreducible]
def a08300 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00148 ^ 1 * a00156 ^ 1)
theorem ha08300 : a08300.IsHomogeneous 139 := by
  unfold a08300
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00480.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 8 * a00003 ^ 1 * a00005 ^ 3 * a00014 ^ 2 * a08300 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00007 ^ 1 * a02222 ^ 1)
theorem ha08301 : a08301.IsHomogeneous 163 := by
  unfold a08301
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 8)).mul (ha00003.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 2)).mul (ha08300.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00007.pow 1)).mul (ha02222.pow 1)))

@[irreducible]
def a08302 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00976 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a02282 ^ 1)
theorem ha08302 : a08302.IsHomogeneous 163 := by
  unfold a08302
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00976.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha02282.pow 1)))

@[irreducible]
def a08303 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00005 ^ 2 * a08302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a08301 ^ 1)
theorem ha08303 : a08303.IsHomogeneous 175 := by
  unfold a08303
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00005.pow 2)).mul (ha08302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha08301.pow 1)))

@[irreducible]
def a08304 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a04415 ^ 1)
theorem ha08304 : a08304.IsHomogeneous 153 := by
  unfold a08304
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02159.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha04415.pow 1)))

@[irreducible]
def a08305 : Poly := (C ((-81 : ℂ) / (100 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08303 ^ 1)
theorem ha08305 : a08305.IsHomogeneous 175 := by
  unfold a08305
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (100 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08304.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08303.pow 1)))

@[irreducible]
def a08306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00155 ^ 1)
theorem ha08306 : a08306.IsHomogeneous 21 := by
  unfold a08306
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a08307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08306 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a04262 ^ 1)
theorem ha08307 : a08307.IsHomogeneous 27 := by
  unfold a08307
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08306.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha04262.pow 1)))

@[irreducible]
def a08308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1)
theorem ha08308 : a08308.IsHomogeneous 12 := by
  unfold a08308
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a08309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00133 ^ 1)
theorem ha08309 : a08309.IsHomogeneous 12 := by
  unfold a08309
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a08310 : Poly := (C ((-1 : ℂ) / (2592 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08307 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a08309 ^ 1)
theorem ha08310 : a08310.IsHomogeneous 27 := by
  unfold a08310
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2592 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08307.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08309.pow 1)))

@[irreducible]
def a08311 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00100 ^ 1 * a08310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04263 ^ 1)
theorem ha08311 : a08311.IsHomogeneous 67 := by
  unfold a08311
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00100.pow 1)).mul (ha08310.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04263.pow 1)))

@[irreducible]
def a08312 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00100 ^ 1 * a04360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a02129 ^ 1)
theorem ha08312 : a08312.IsHomogeneous 121 := by
  unfold a08312
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha04360.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha02129.pow 1)))

@[irreducible]
def a08313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08312 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a08311 ^ 1)
theorem ha08313 : a08313.IsHomogeneous 121 := by
  unfold a08313
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08312.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha08311.pow 1)))

@[irreducible]
def a08314 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00393 ^ 1 * a02236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00950 ^ 1 * a01092 ^ 1)
theorem ha08314 : a08314.IsHomogeneous 134 := by
  unfold a08314
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00393.pow 1)).mul (ha02236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00950.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a08315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08314 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a08313 ^ 1)
theorem ha08315 : a08315.IsHomogeneous 134 := by
  unfold a08315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08314.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08313.pow 1)))

@[irreducible]
def a08316 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00982 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a02295 ^ 1)
theorem ha08316 : a08316.IsHomogeneous 123 := by
  unfold a08316
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00982.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a08317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a08316 ^ 1) + (C ((5 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08315 ^ 1)
theorem ha08317 : a08317.IsHomogeneous 136 := by
  unfold a08317
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08315.pow 1)))

@[irreducible]
def a08318 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a02166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a04430 ^ 1)
theorem ha08318 : a08318.IsHomogeneous 145 := by
  unfold a08318
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha02166.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha04430.pow 1)))

@[irreducible]
def a08319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08318 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a08317 ^ 1)
theorem ha08319 : a08319.IsHomogeneous 145 := by
  unfold a08319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08318.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha08317.pow 1)))

@[irreducible]
def a08320 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00301 ^ 1)
theorem ha08320 : a08320.IsHomogeneous 102 := by
  unfold a08320
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00131.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00301.pow 1)))

@[irreducible]
def a08321 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00146 ^ 1 * a04368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a02133 ^ 1)
theorem ha08321 : a08321.IsHomogeneous 122 := by
  unfold a08321
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha04368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a08322 : Poly := (C ((-1 : ℂ) / (25 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a08320 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08321 ^ 1)
theorem ha08322 : a08322.IsHomogeneous 122 := by
  unfold a08322
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (25 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha08320.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08321.pow 1)))

@[irreducible]
def a08323 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00387 ^ 1 * a02242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00953 ^ 1 * a01079 ^ 1)
theorem ha08323 : a08323.IsHomogeneous 126 := by
  unfold a08323
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00953.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a08324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08323 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08322 ^ 1)
theorem ha08324 : a08324.IsHomogeneous 132 := by
  unfold a08324
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08323.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08322.pow 1)))

@[irreducible]
def a08325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a02278 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00974 ^ 1 * a01052 ^ 1)
theorem ha08325 : a08325.IsHomogeneous 116 := by
  unfold a08325
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02278.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00974.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a08326 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 2 * a08325 ^ 1)
theorem ha08326 : a08326.IsHomogeneous 133 := by
  unfold a08326
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08325.pow 1)))

@[irreducible]
def a08327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a04411 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a02157 ^ 1)
theorem ha08327 : a08327.IsHomogeneous 105 := by
  unfold a08327
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha04411.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha02157.pow 1)))

@[irreducible]
def a08328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08326 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 3 * a08327 ^ 1)
theorem ha08328 : a08328.IsHomogeneous 133 := by
  unfold a08328
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08326.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha08327.pow 1)))

@[irreducible]
def a08329 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a02250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02248 ^ 1)
theorem ha08329 : a08329.IsHomogeneous 12 := by
  unfold a08329
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha02250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02248.pow 1)))

@[irreducible]
def a08330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08329 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00260 ^ 1 * a04272 ^ 1)
theorem ha08330 : a08330.IsHomogeneous 48 := by
  unfold a08330
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08329.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00260.pow 1)).mul (ha04272.pow 1)))

@[irreducible]
def a08331 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04378 ^ 1)
theorem ha08331 : a08331.IsHomogeneous 74 := by
  unfold a08331
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04378.pow 1)))

@[irreducible]
def a08332 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a08330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08331 ^ 1)
theorem ha08332 : a08332.IsHomogeneous 74 := by
  unfold a08332
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha08330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08331.pow 1)))

@[irreducible]
def a08333 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02252 ^ 1)
theorem ha08333 : a08333.IsHomogeneous 84 := by
  unfold a08333
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00958.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a08334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08333 ^ 1) + (C ((1 : ℂ) / (192 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08332 ^ 1)
theorem ha08334 : a08334.IsHomogeneous 84 := by
  unfold a08334
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08333.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (192 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08332.pow 1)))

@[irreducible]
def a08335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01060 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00375 ^ 1)
theorem ha08335 : a08335.IsHomogeneous 80 := by
  unfold a08335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01060.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00375.pow 1)))

@[irreducible]
def a08336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08335 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08334 ^ 1)
theorem ha08336 : a08336.IsHomogeneous 85 := by
  unfold a08336
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08334.pow 1)))

@[irreducible]
def a08337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00465 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00139 ^ 1 * a00173 ^ 1)
theorem ha08337 : a08337.IsHomogeneous 61 := by
  unfold a08337
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00465.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00139.pow 1)).mul (ha00173.pow 1)))

@[irreducible]
def a08338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08336 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08337 ^ 1)
theorem ha08338 : a08338.IsHomogeneous 85 := by
  unfold a08338
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08336.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08337.pow 1)))

@[irreducible]
def a08339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00035 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00160 ^ 1)
theorem ha08339 : a08339.IsHomogeneous 84 := by
  unfold a08339
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00035.pow 1)).mul (ha00300.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00160.pow 1)))

@[irreducible]
def a08340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08338 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08339 ^ 1)
theorem ha08340 : a08340.IsHomogeneous 85 := by
  unfold a08340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08338.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08339.pow 1)))

@[irreducible]
def a08341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6)
theorem ha08341 : a08341.IsHomogeneous 6 := by
  unfold a08341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a08342 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08341 ^ 1)
theorem ha08342 : a08342.IsHomogeneous 25 := by
  unfold a08342
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02250.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08341.pow 1)))

@[irreducible]
def a08343 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a04278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08342 ^ 1)
theorem ha08343 : a08343.IsHomogeneous 61 := by
  unfold a08343
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha04278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08342.pow 1)))

@[irreducible]
def a08344 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00241 ^ 1 * a02144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04390 ^ 1)
theorem ha08344 : a08344.IsHomogeneous 80 := by
  unfold a08344
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00241.pow 1)).mul (ha02144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04390.pow 1)))

@[irreducible]
def a08345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08344 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a08343 ^ 1)
theorem ha08345 : a08345.IsHomogeneous 80 := by
  unfold a08345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08344.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha08343.pow 1)))

@[irreducible]
def a08346 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02261 ^ 1)
theorem ha08346 : a08346.IsHomogeneous 84 := by
  unfold a08346
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02261.pow 1)))

@[irreducible]
def a08347 : Poly := (C ((-108 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08345 ^ 1)
theorem ha08347 : a08347.IsHomogeneous 85 := by
  unfold a08347
  exact ((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08346.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08345.pow 1)))

@[irreducible]
def a08348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01067 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00379 ^ 1)
theorem ha08348 : a08348.IsHomogeneous 80 := by
  unfold a08348
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01067.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00379.pow 1)))

@[irreducible]
def a08349 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08347 ^ 1)
theorem ha08349 : a08349.IsHomogeneous 85 := by
  unfold a08349
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08347.pow 1)))

@[irreducible]
def a08350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00469 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00141 ^ 1 * a00173 ^ 1)
theorem ha08350 : a08350.IsHomogeneous 61 := by
  unfold a08350
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00141.pow 1)).mul (ha00173.pow 1)))

@[irreducible]
def a08351 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08349 ^ 1)
theorem ha08351 : a08351.IsHomogeneous 85 := by
  unfold a08351
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08349.pow 1)))

@[irreducible]
def a08352 : Poly := (C ((-108 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08351 ^ 1)
theorem ha08352 : a08352.IsHomogeneous 85 := by
  unfold a08352
  exact ((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08339.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08351.pow 1)))

@[irreducible]
def a08353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08340 ^ 1) + (C ((1 : ℂ) / (45 : ℂ)) * a08352 ^ 1)
theorem ha08353 : a08353.IsHomogeneous 85 := by
  unfold a08353
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (45 : ℂ))).mul (ha08352.pow 1)))

@[irreducible]
def a08354 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08341 ^ 1)
theorem ha08354 : a08354.IsHomogeneous 25 := by
  unfold a08354
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02250.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08341.pow 1)))

@[irreducible]
def a08355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08354 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02248 ^ 1)
theorem ha08355 : a08355.IsHomogeneous 25 := by
  unfold a08355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08354.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02248.pow 1)))

@[irreducible]
def a08356 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a04286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08355 ^ 1)
theorem ha08356 : a08356.IsHomogeneous 61 := by
  unfold a08356
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha04286.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08355.pow 1)))

@[irreducible]
def a08357 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00241 ^ 1 * a02152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04402 ^ 1)
theorem ha08357 : a08357.IsHomogeneous 80 := by
  unfold a08357
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00241.pow 1)).mul (ha02152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04402.pow 1)))

@[irreducible]
def a08358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08357 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a08356 ^ 1)
theorem ha08358 : a08358.IsHomogeneous 80 := by
  unfold a08358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08357.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha08356.pow 1)))

@[irreducible]
def a08359 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02271 ^ 1)
theorem ha08359 : a08359.IsHomogeneous 84 := by
  unfold a08359
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02271.pow 1)))

@[irreducible]
def a08360 : Poly := (C ((-81 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08358 ^ 1)
theorem ha08360 : a08360.IsHomogeneous 85 := by
  unfold a08360
  exact ((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08359.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08358.pow 1)))

@[irreducible]
def a08361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01074 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00384 ^ 1)
theorem ha08361 : a08361.IsHomogeneous 80 := by
  unfold a08361
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01074.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00384.pow 1)))

@[irreducible]
def a08362 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a08361 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08360 ^ 1)
theorem ha08362 : a08362.IsHomogeneous 85 := by
  unfold a08362
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha08361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08360.pow 1)))

@[irreducible]
def a08363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00473 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00144 ^ 1 * a00173 ^ 1)
theorem ha08363 : a08363.IsHomogeneous 61 := by
  unfold a08363
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00144.pow 1)).mul (ha00173.pow 1)))

@[irreducible]
def a08364 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a08363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08362 ^ 1)
theorem ha08364 : a08364.IsHomogeneous 85 := by
  unfold a08364
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08362.pow 1)))

@[irreducible]
def a08365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08353 ^ 1) + (C ((4 : ℂ) / (135 : ℂ)) * a08364 ^ 1)
theorem ha08365 : a08365.IsHomogeneous 85 := by
  unfold a08365
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (135 : ℂ))).mul (ha08364.pow 1)))

@[irreducible]
def a08366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a08365 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a04291 ^ 1)
theorem ha08366 : a08366.IsHomogeneous 103 := by
  unfold a08366
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha08365.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha04291.pow 1)))

@[irreducible]
def a08367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 4 * a08366 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a08328 ^ 1)
theorem ha08367 : a08367.IsHomogeneous 133 := by
  unfold a08367
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha08366.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha08328.pow 1)))

@[irreducible]
def a08368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08367 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04292 ^ 1)
theorem ha08368 : a08368.IsHomogeneous 133 := by
  unfold a08368
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08367.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04292.pow 1)))

@[irreducible]
def a08369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08319 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a08368 ^ 1)
theorem ha08369 : a08369.IsHomogeneous 145 := by
  unfold a08369
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08319.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha08368.pow 1)))

@[irreducible]
def a08370 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a04293 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a08369 ^ 1)
theorem ha08370 : a08370.IsHomogeneous 175 := by
  unfold a08370
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha04293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha08369.pow 1)))

@[irreducible]
def a08371 : Poly := (C ((-27 : ℂ) / (20 : ℂ)) * a08370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08305 ^ 1)
theorem ha08371 : a08371.IsHomogeneous 175 := by
  unfold a08371
  exact (((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (20 : ℂ))).mul (ha08370.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08305.pow 1)))

@[irreducible]
def a08372 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a04445 ^ 1)
theorem ha08372 : a08372.IsHomogeneous 508 := by
  unfold a08372
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha02173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha04445.pow 1)))

@[irreducible]
def a08373 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00988 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a02308 ^ 1)
theorem ha08373 : a08373.IsHomogeneous 485 := by
  unfold a08373
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00988.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a08374 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00986 ^ 1 * a01103 ^ 1)
theorem ha08374 : a08374.IsHomogeneous 461 := by
  unfold a08374
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00986.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a08375 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a04441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a02171 ^ 1)
theorem ha08375 : a08375.IsHomogeneous 387 := by
  unfold a08375
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha04441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha02171.pow 1)))

@[irreducible]
def a08376 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a02302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00985 ^ 1)
theorem ha08376 : a08376.IsHomogeneous 142 := by
  unfold a08376
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha02302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00985.pow 1)))

@[irreducible]
def a08377 : Poly := (C ((-4 : ℂ) / (45 : ℂ)) * a00000 ^ 3 * a00002 ^ 4 * a00003 ^ 2 * a00005 ^ 1 * a08376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a02289 ^ 1)
theorem ha08377 : a08377.IsHomogeneous 152 := by
  unfold a08377
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (45 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00005.pow 1)).mul (ha08376.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02289.pow 1)))

@[irreducible]
def a08378 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04439 ^ 1)
theorem ha08378 : a08378.IsHomogeneous 140 := by
  unfold a08378
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04439.pow 1)))

@[irreducible]
def a08379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a08378 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a08377 ^ 1)
theorem ha08379 : a08379.IsHomogeneous 153 := by
  unfold a08379
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08378.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha08377.pow 1)))

@[irreducible]
def a08380 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00035 ^ 1 * a00260 ^ 1)
theorem ha08380 : a08380.IsHomogeneous 66 := by
  unfold a08380
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00160.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00035.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a08381 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00241 ^ 1)
theorem ha08381 : a08381.IsHomogeneous 74 := by
  unfold a08381
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a08382 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00211 ^ 1)
theorem ha08382 : a08382.IsHomogeneous 85 := by
  unfold a08382
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a08383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 4 * a00003 ^ 1 * a00005 ^ 1 * a08381 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00014 ^ 2 * a08380 ^ 1)
theorem ha08383 : a08383.IsHomogeneous 80 := by
  unfold a08383
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha08381.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha08380.pow 1)))

@[irreducible]
def a08384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08382 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00001 ^ 3 * a00004 ^ 2 * a08383 ^ 1)
theorem ha08384 : a08384.IsHomogeneous 85 := by
  unfold a08384
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08382.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha08383.pow 1)))

@[irreducible]
def a08385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08382 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08384 ^ 1)
theorem ha08385 : a08385.IsHomogeneous 85 := by
  unfold a08385
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08382.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08384.pow 1)))

@[irreducible]
def a08386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08385 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00001 ^ 3 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a08381 ^ 1)
theorem ha08386 : a08386.IsHomogeneous 85 := by
  unfold a08386
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08385.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha08381.pow 1)))

@[irreducible]
def a08387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08386 ^ 1) + (C ((9 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00014 ^ 2 * a08380 ^ 1)
theorem ha08387 : a08387.IsHomogeneous 85 := by
  unfold a08387
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08386.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00014.pow 2)).mul (ha08380.pow 1)))

@[irreducible]
def a08388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a08387 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04301 ^ 1)
theorem ha08388 : a08388.IsHomogeneous 121 := by
  unfold a08388
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha08387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04301.pow 1)))

@[irreducible]
def a08389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02166 ^ 1)
theorem ha08389 : a08389.IsHomogeneous 134 := by
  unfold a08389
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04430.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a08390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a08389 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a08388 ^ 1)
theorem ha08390 : a08390.IsHomogeneous 135 := by
  unfold a08390
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha08389.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha08388.pow 1)))

@[irreducible]
def a08391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00982 ^ 1)
theorem ha08391 : a08391.IsHomogeneous 135 := by
  unfold a08391
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a08392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08390 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a08391 ^ 1)
theorem ha08392 : a08392.IsHomogeneous 135 := by
  unfold a08392
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha08391.pow 1)))

@[irreducible]
def a08393 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00393 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01092 ^ 1)
theorem ha08393 : a08393.IsHomogeneous 134 := by
  unfold a08393
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00393.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a08394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08392 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a08393 ^ 1)
theorem ha08394 : a08394.IsHomogeneous 135 := by
  unfold a08394
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha08393.pow 1)))

@[irreducible]
def a08395 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00484 ^ 1)
theorem ha08395 : a08395.IsHomogeneous 110 := by
  unfold a08395
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a08396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08394 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08395 ^ 1)
theorem ha08396 : a08396.IsHomogeneous 135 := by
  unfold a08396
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08394.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08395.pow 1)))

@[irreducible]
def a08397 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00035 ^ 1 * a00260 ^ 1)
theorem ha08397 : a08397.IsHomogeneous 66 := by
  unfold a08397
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00160.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00035.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a08398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08396 ^ 1) + (C ((108 : ℂ) / (25 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a08397 ^ 1)
theorem ha08398 : a08398.IsHomogeneous 135 := by
  unfold a08398
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08396.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (25 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha08397.pow 1)))

@[irreducible]
def a08399 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a04306 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a08398 ^ 1)
theorem ha08399 : a08399.IsHomogeneous 159 := by
  unfold a08399
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha04306.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha08398.pow 1)))

@[irreducible]
def a08400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08399 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00004 ^ 2 * a00005 ^ 1 * a08379 ^ 1)
theorem ha08400 : a08400.IsHomogeneous 159 := by
  unfold a08400
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08399.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha08379.pow 1)))

@[irreducible]
def a08401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a04307 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08400 ^ 1)
theorem ha08401 : a08401.IsHomogeneous 267 := by
  unfold a08401
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha04307.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08400.pow 1)))

@[irreducible]
def a08402 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a08372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a08373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 2 * a08374 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 1 * a08375 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 6 * a00042 ^ 4 * a00100 ^ 2 * a00126 ^ 1 * a08401 ^ 1)
theorem ha08402 : a08402.IsHomogeneous 509 := by
  unfold a08402
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha08372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha08373.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 2)).mul (ha08374.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha08375.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00042.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha08401.pow 1)))

@[irreducible]
def a08403 : Poly := (C ((-1 : ℂ) / (30 : ℂ)) * a00001 ^ 7 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 5 * a08371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08402 ^ 1)
theorem ha08403 : a08403.IsHomogeneous 509 := by
  unfold a08403
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (30 : ℂ))).mul (ha00001.pow 7)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha08371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08402.pow 1)))

@[irreducible]
def a08404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a04309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08403 ^ 1)
theorem ha08404 : a08404.IsHomogeneous 509 := by
  unfold a08404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha04309.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08403.pow 1)))

@[irreducible]
def a08405 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a04309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a08404 ^ 1)
theorem ha08405 : a08405.IsHomogeneous 935 := by
  unfold a08405
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha04309.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha08404.pow 1)))

@[irreducible]
def a08406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00455 ^ 1)
theorem ha08406 : a08406.IsHomogeneous 12 := by
  unfold a08406
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a08407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08406 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02310 ^ 1)
theorem ha08407 : a08407.IsHomogeneous 31 := by
  unfold a08407
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08406.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02310.pow 1)))

@[irreducible]
def a08408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08407 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02310 ^ 1)
theorem ha08408 : a08408.IsHomogeneous 31 := by
  unfold a08408
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08407.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02310.pow 1)))

@[irreducible]
def a08409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08406 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08408 ^ 1)
theorem ha08409 : a08409.IsHomogeneous 31 := by
  unfold a08409
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08408.pow 1)))

@[irreducible]
def a08410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a08409 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00299 ^ 1 * a04312 ^ 1)
theorem ha08410 : a08410.IsHomogeneous 49 := by
  unfold a08410
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha08409.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00299.pow 1)).mul (ha04312.pow 1)))

@[irreducible]
def a08411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a04451 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a02177 ^ 1)
theorem ha08411 : a08411.IsHomogeneous 61 := by
  unfold a08411
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha04451.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha02177.pow 1)))

@[irreducible]
def a08412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00006 ^ 1 * a00014 ^ 1 * a08410 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a08411 ^ 1)
theorem ha08412 : a08412.IsHomogeneous 63 := by
  unfold a08412
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha08410.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha08411.pow 1)))

@[irreducible]
def a08413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a02313 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00025 ^ 1 * a00991 ^ 1 * a01052 ^ 1)
theorem ha08413 : a08413.IsHomogeneous 67 := by
  unfold a08413
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02313.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00991.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a08414 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08412 ^ 1)
theorem ha08414 : a08414.IsHomogeneous 69 := by
  unfold a08414
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08412.pow 1)))

@[irreducible]
def a08415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00953 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00400 ^ 1 * a02242 ^ 1)
theorem ha08415 : a08415.IsHomogeneous 73 := by
  unfold a08415
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00953.pow 1)).mul (ha01107.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a08416 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08415 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08414 ^ 1)
theorem ha08416 : a08416.IsHomogeneous 75 := by
  unfold a08416
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08415.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08414.pow 1)))

@[irreducible]
def a08417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a02133 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a04368 ^ 1)
theorem ha08417 : a08417.IsHomogeneous 61 := by
  unfold a08417
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha02133.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha04368.pow 1)))

@[irreducible]
def a08418 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 1 * a08417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08416 ^ 1)
theorem ha08418 : a08418.IsHomogeneous 75 := by
  unfold a08418
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha08417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08416.pow 1)))

@[irreducible]
def a08419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00126 ^ 1 * a00131 ^ 1)
theorem ha08419 : a08419.IsHomogeneous 36 := by
  unfold a08419
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00126.pow 1)).mul (ha00131.pow 1)))

@[irreducible]
def a08420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08418 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00002 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00007 ^ 1 * a00126 ^ 1 * a08419 ^ 1)
theorem ha08420 : a08420.IsHomogeneous 81 := by
  unfold a08420
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08418.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00126.pow 1)).mul (ha08419.pow 1)))

@[irreducible]
def a08421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08420 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a04317 ^ 1)
theorem ha08421 : a08421.IsHomogeneous 87 := by
  unfold a08421
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08420.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha04317.pow 1)))

@[irreducible]
def a08422 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00484 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04468 ^ 1)
theorem ha08422 : a08422.IsHomogeneous 352 := by
  unfold a08422
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00484.pow 1)).mul (ha02183.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04468.pow 1)))

@[irreducible]
def a08423 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00996 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a02327 ^ 1)
theorem ha08423 : a08423.IsHomogeneous 353 := by
  unfold a08423
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00996.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a08424 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00982 ^ 1 * a01118 ^ 1)
theorem ha08424 : a08424.IsHomogeneous 304 := by
  unfold a08424
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00982.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a08425 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a04430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a02166 ^ 1)
theorem ha08425 : a08425.IsHomogeneous 254 := by
  unfold a08425
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha04430.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a08426 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a08387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a04301 ^ 1)
theorem ha08426 : a08426.IsHomogeneous 169 := by
  unfold a08426
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha08387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha04301.pow 1)))

@[irreducible]
def a08427 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a00100 ^ 3 * a00126 ^ 1 * a08426 ^ 1) + (C ((-4 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a08422 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a08424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08423 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00004 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a08425 ^ 1)
theorem ha08427 : a08427.IsHomogeneous 353 := by
  unfold a08427
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00100.pow 3)).mul (ha00126.pow 1)).mul (ha08426.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha08422.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha08424.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08423.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00004.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha08425.pow 1)))

@[irreducible]
def a08428 : Poly := (C ((-3 : ℂ) / (500 : ℂ)) * a00001 ^ 11 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 5 * a00100 ^ 6 * a08421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08427 ^ 1)
theorem ha08428 : a08428.IsHomogeneous 353 := by
  unfold a08428
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (500 : ℂ))).mul (ha00001.pow 11)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 5)).mul (ha00100.pow 6)).mul (ha08421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08427.pow 1)))

@[irreducible]
def a08429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08428 ^ 1)
theorem ha08429 : a08429.IsHomogeneous 353 := by
  unfold a08429
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08428.pow 1)))

@[irreducible]
def a08430 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a08429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a04319 ^ 1)
theorem ha08430 : a08430.IsHomogeneous 779 := by
  unfold a08430
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha08429.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha04319.pow 1)))

@[irreducible]
def a08431 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a08296 ^ 1) + (C ((-32 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 6 * a00100 ^ 1 * a08297 ^ 1) + (C ((-16 : ℂ) / (27 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 6 * a08430 ^ 1) + (C ((-1 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 2 * a08294 ^ 1) + (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 3 * a00042 ^ 4 * a00100 ^ 3 * a08293 ^ 1) + (C ((-1 : ℂ) / (9 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 4 * a00042 ^ 6 * a00100 ^ 2 * a08295 ^ 1) + (C ((-1 : ℂ) / (1875 : ℂ)) * a00001 ^ 12 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 1 * a00014 ^ 6 * a00042 ^ 6 * a00100 ^ 7 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00042 ^ 1 * a08298 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 4 * a08405 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 6 * a08299 ^ 1)
theorem ha08431 : a08431.IsHomogeneous 963 := by
  unfold a08431
  exact ((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha08296.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 6)).mul (ha00100.pow 1)).mul (ha08297.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha08430.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha08294.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 3)).mul (ha08293.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 6)).mul (ha00100.pow 2)).mul (ha08295.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1875 : ℂ))).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00014.pow 6)).mul (ha00042.pow 6)).mul (ha00100.pow 7)).mul (ha02213.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00042.pow 1)).mul (ha08298.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 4)).mul (ha08405.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 6)).mul (ha08299.pow 1)))

@[irreducible]
def a08432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1)
theorem ha08432 : a08432.IsHomogeneous 6 := by
  unfold a08432
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a08433 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08432 ^ 1)
theorem ha08433 : a08433.IsHomogeneous 25 := by
  unfold a08433
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02332.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08432.pow 1)))

@[irreducible]
def a08434 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a02332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02330 ^ 1)
theorem ha08434 : a08434.IsHomogeneous 12 := by
  unfold a08434
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha02332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02330.pow 1)))

@[irreducible]
def a08435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08433 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a08434 ^ 1)
theorem ha08435 : a08435.IsHomogeneous 25 := by
  unfold a08435
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08433.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha08434.pow 1)))

@[irreducible]
def a08436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00524 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00596 ^ 1)
theorem ha08436 : a08436.IsHomogeneous 24 := by
  unfold a08436
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00524.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00596.pow 1)))

@[irreducible]
def a08437 : Poly := (C ((-1 : ℂ) / (30 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a00524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 2 * a00531 ^ 1)
theorem ha08437 : a08437.IsHomogeneous 36 := by
  unfold a08437
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (30 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00524.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00531.pow 1)))

@[irreducible]
def a08438 : Poly := (C ((-1 : ℂ) / (30 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a08436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08437 ^ 1)
theorem ha08438 : a08438.IsHomogeneous 36 := by
  unfold a08438
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (30 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha08436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08437.pow 1)))

@[irreducible]
def a08439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00156 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00510 ^ 1)
theorem ha08439 : a08439.IsHomogeneous 18 := by
  unfold a08439
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00156.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a08440 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a02362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a08439 ^ 1) + (C ((7 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00014 ^ 1 * a00551 ^ 1)
theorem ha08440 : a08440.IsHomogeneous 37 := by
  unfold a08440
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha02362.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08439.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha00551.pow 1)))

@[irreducible]
def a08441 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a08440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a08438 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00014 ^ 1 * a02353 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a08435 ^ 1)
theorem ha08441 : a08441.IsHomogeneous 37 := by
  unfold a08441
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha08440.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha08438.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha02353.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha08435.pow 1)))

@[irreducible]
def a08442 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a02203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04499 ^ 1)
theorem ha08442 : a08442.IsHomogeneous 328 := by
  unfold a08442
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha02203.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04499.pow 1)))

@[irreducible]
def a08443 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a01026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02376 ^ 1)
theorem ha08443 : a08443.IsHomogeneous 280 := by
  unfold a08443
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha01026.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02376.pow 1)))

@[irreducible]
def a08444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01180 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1 * a00445 ^ 1)
theorem ha08444 : a08444.IsHomogeneous 230 := by
  unfold a08444
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01180.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).mul (ha00445.pow 1)))

@[irreducible]
def a08445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00039 ^ 1 * a00931 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00173 ^ 1 * a00362 ^ 1)
theorem ha08445 : a08445.IsHomogeneous 170 := by
  unfold a08445
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00039.pow 1)).mul (ha00931.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00173.pow 1)).mul (ha00362.pow 1)))

@[irreducible]
def a08446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00035 ^ 1 * a00327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00160 ^ 1)
theorem ha08446 : a08446.IsHomogeneous 126 := by
  unfold a08446
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00035.pow 1)).mul (ha00327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00160.pow 1)))

@[irreducible]
def a08447 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a08443 ^ 1) + (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 6 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 6 * a00100 ^ 3 * a08445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a08444 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a08442 ^ 1) + (C ((54 : ℂ) / (25 : ℂ)) * a00000 ^ 1 * a00001 ^ 7 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 8 * a00100 ^ 4 * a08446 ^ 1)
theorem ha08447 : a08447.IsHomogeneous 329 := by
  unfold a08447
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha08443.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00100.pow 3)).mul (ha08445.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha08444.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha08442.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (25 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 7)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 8)).mul (ha00100.pow 4)).mul (ha08446.pow 1)))

end CycleQ2Concrete
