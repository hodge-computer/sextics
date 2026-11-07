import Proposal.CurrentAtoms027

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a08960 : Poly := (C ((-1 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a08953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08959 ^ 1)
theorem ha08960 : a08960.IsHomogeneous 161 := by
  unfold a08960
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha08953.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08959.pow 1)))

@[irreducible]
def a08961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02280 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a04658 ^ 1)
theorem ha08961 : a08961.IsHomogeneous 139 := by
  unfold a08961
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha04658.pow 1)))

@[irreducible]
def a08962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02280 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00975 ^ 1 * a01841 ^ 1)
theorem ha08962 : a08962.IsHomogeneous 139 := by
  unfold a08962
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00975.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a08963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08961 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08962 ^ 1)
theorem ha08963 : a08963.IsHomogeneous 139 := by
  unfold a08963
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08961.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08962.pow 1)))

@[irreducible]
def a08964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a02242 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a04588 ^ 1)
theorem ha08964 : a08964.IsHomogeneous 124 := by
  unfold a08964
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha02242.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha04588.pow 1)))

@[irreducible]
def a08965 : Poly := (C ((-7 : ℂ) / (120 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00007 ^ 1 * a01847 ^ 1) + (C ((1 : ℂ) / (4320 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00007 ^ 1)
theorem ha08965 : a08965.IsHomogeneous 21 := by
  unfold a08965
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (120 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha01847.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4320 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00007.pow 1)))

@[irreducible]
def a08966 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a08965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a04588 ^ 1)
theorem ha08966 : a08966.IsHomogeneous 118 := by
  unfold a08966
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha08965.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha04588.pow 1)))

@[irreducible]
def a08967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08964 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a08966 ^ 1)
theorem ha08967 : a08967.IsHomogeneous 124 := by
  unfold a08967
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08964.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha08966.pow 1)))

@[irreducible]
def a08968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a02242 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00953 ^ 1 * a01917 ^ 1)
theorem ha08968 : a08968.IsHomogeneous 130 := by
  unfold a08968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha02242.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00953.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a08969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08964 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08968 ^ 1)
theorem ha08969 : a08969.IsHomogeneous 130 := by
  unfold a08969
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08964.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08968.pow 1)))

@[irreducible]
def a08970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08969 ^ 1)
theorem ha08970 : a08970.IsHomogeneous 130 := by
  unfold a08970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08969.pow 1)))

@[irreducible]
def a08971 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01052 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00476 ^ 1 * a02441 ^ 1)
theorem ha08971 : a08971.IsHomogeneous 126 := by
  unfold a08971
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01052.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a08972 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00146 ^ 1 * a04950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a02441 ^ 1)
theorem ha08972 : a08972.IsHomogeneous 120 := by
  unfold a08972
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha04950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a08973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a08972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08971 ^ 1)
theorem ha08973 : a08973.IsHomogeneous 126 := by
  unfold a08973
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha08972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08971.pow 1)))

@[irreducible]
def a08974 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a01052 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a02806 ^ 1)
theorem ha08974 : a08974.IsHomogeneous 126 := by
  unfold a08974
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha01052.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02806.pow 1)))

@[irreducible]
def a08975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08971 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a08974 ^ 1)
theorem ha08975 : a08975.IsHomogeneous 126 := by
  unfold a08975
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08971.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha08974.pow 1)))

@[irreducible]
def a08976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08973 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08975 ^ 1)
theorem ha08976 : a08976.IsHomogeneous 126 := by
  unfold a08976
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08973.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08975.pow 1)))

@[irreducible]
def a08977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a08976 ^ 1) + (C ((864 : ℂ) / (125 : ℂ)) * a00001 ^ 1 * a08970 ^ 1)
theorem ha08977 : a08977.IsHomogeneous 131 := by
  unfold a08977
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha08976.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((864 : ℂ) / (125 : ℂ))).mul (ha00001.pow 1)).mul (ha08970.pow 1)))

@[irreducible]
def a08978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a02493 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01079 ^ 1 * a01228 ^ 1)
theorem ha08978 : a08978.IsHomogeneous 123 := by
  unfold a08978
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha02493.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01079.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a08979 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a02754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01079 ^ 1 * a01228 ^ 1)
theorem ha08979 : a08979.IsHomogeneous 117 := by
  unfold a08979
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha02754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01079.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a08980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08978 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a08979 ^ 1)
theorem ha08980 : a08980.IsHomogeneous 123 := by
  unfold a08980
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha08979.pow 1)))

@[irreducible]
def a08981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a05039 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00461 ^ 1 * a02493 ^ 1)
theorem ha08981 : a08981.IsHomogeneous 130 := by
  unfold a08981
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha05039.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha02493.pow 1)))

@[irreducible]
def a08982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08981 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a08978 ^ 1)
theorem ha08982 : a08982.IsHomogeneous 130 := by
  unfold a08982
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08981.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha08978.pow 1)))

@[irreducible]
def a08983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08982 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a08980 ^ 1)
theorem ha08983 : a08983.IsHomogeneous 130 := by
  unfold a08983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08982.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha08980.pow 1)))

@[irreducible]
def a08984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08977 ^ 1) + (C ((864 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a08983 ^ 1)
theorem ha08984 : a08984.IsHomogeneous 131 := by
  unfold a08984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08977.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((864 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha08983.pow 1)))

@[irreducible]
def a08985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a04655 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a02278 ^ 1)
theorem ha08985 : a08985.IsHomogeneous 118 := by
  unfold a08985
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha04655.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha02278.pow 1)))

@[irreducible]
def a08986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a02278 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00974 ^ 1 * a01903 ^ 1)
theorem ha08986 : a08986.IsHomogeneous 112 := by
  unfold a08986
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha02278.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00974.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a08987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08985 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a08986 ^ 1)
theorem ha08987 : a08987.IsHomogeneous 118 := by
  unfold a08987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08985.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha08986.pow 1)))

@[irreducible]
def a08988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04610 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a02252 ^ 1)
theorem ha08988 : a08988.IsHomogeneous 88 := by
  unfold a08988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04610.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a08989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02252 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00958 ^ 1 * a01702 ^ 1)
theorem ha08989 : a08989.IsHomogeneous 87 := by
  unfold a08989
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02252.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00958.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a08990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08988 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a08989 ^ 1)
theorem ha08990 : a08990.IsHomogeneous 88 := by
  unfold a08990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha08989.pow 1)))

@[irreducible]
def a08991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a02413 ^ 1)
theorem ha08991 : a08991.IsHomogeneous 18 := by
  unfold a08991
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha02413.pow 1)))

@[irreducible]
def a08992 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00368 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01041 ^ 1)
theorem ha08992 : a08992.IsHomogeneous 18 := by
  unfold a08992
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00368.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a08993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08992 ^ 1)
theorem ha08993 : a08993.IsHomogeneous 18 := by
  unfold a08993
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08992.pow 1)))

@[irreducible]
def a08994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02413 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a04894 ^ 1)
theorem ha08994 : a08994.IsHomogeneous 24 := by
  unfold a08994
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a08995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08991 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a08994 ^ 1)
theorem ha08995 : a08995.IsHomogeneous 24 := by
  unfold a08995
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha08994.pow 1)))

@[irreducible]
def a08996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a08993 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08995 ^ 1)
theorem ha08996 : a08996.IsHomogeneous 24 := by
  unfold a08996
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha08993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08995.pow 1)))

@[irreducible]
def a08997 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02771 ^ 1)
theorem ha08997 : a08997.IsHomogeneous 52 := by
  unfold a08997
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08996.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02771.pow 1)))

@[irreducible]
def a08998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00506 ^ 1)
theorem ha08998 : a08998.IsHomogeneous 24 := by
  unfold a08998
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a08999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00455 ^ 1 * a00506 ^ 1)
theorem ha08999 : a08999.IsHomogeneous 24 := by
  unfold a08999
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a09000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08998 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a08999 ^ 1)
theorem ha09000 : a09000.IsHomogeneous 24 := by
  unfold a09000
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08998.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha08999.pow 1)))

@[irreducible]
def a09001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01207 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a02710 ^ 1)
theorem ha09001 : a09001.IsHomogeneous 18 := by
  unfold a09001
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01207.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha02710.pow 1)))

@[irreducible]
def a09002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09001 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08999 ^ 1)
theorem ha09002 : a09002.IsHomogeneous 24 := by
  unfold a09002
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08999.pow 1)))

@[irreducible]
def a09003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09000 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a09002 ^ 1)
theorem ha09003 : a09003.IsHomogeneous 24 := by
  unfold a09003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09000.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha09002.pow 1)))

@[irreducible]
def a09004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08997 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09003 ^ 1)
theorem ha09004 : a09004.IsHomogeneous 52 := by
  unfold a09004
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08997.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09003.pow 1)))

@[irreducible]
def a09005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02777 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a09004 ^ 1)
theorem ha09005 : a09005.IsHomogeneous 52 := by
  unfold a09005
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02777.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha09004.pow 1)))

@[irreducible]
def a09006 : Poly := (C ((-27 : ℂ) / (20 : ℂ)) * a00260 ^ 1 * a04610 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09005 ^ 1)
theorem ha09006 : a09006.IsHomogeneous 88 := by
  unfold a09006
  exact ((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (20 : ℂ))).mul (ha00260.pow 1)).mul (ha04610.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09005.pow 1)))

@[irreducible]
def a09007 : Poly := (C ((-20 : ℂ) / (27 : ℂ)) * a09006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08988 ^ 1)
theorem ha09007 : a09007.IsHomogeneous 88 := by
  unfold a09007
  exact (((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (27 : ℂ))).mul (ha09006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08988.pow 1)))

@[irreducible]
def a09008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08990 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09007 ^ 1)
theorem ha09008 : a09008.IsHomogeneous 88 := by
  unfold a09008
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08990.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09007.pow 1)))

@[irreducible]
def a09009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01060 ^ 1)
theorem ha09009 : a09009.IsHomogeneous 96 := by
  unfold a09009
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a09010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00375 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01060 ^ 1)
theorem ha09010 : a09010.IsHomogeneous 96 := by
  unfold a09010
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00375.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a09011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09010 ^ 1)
theorem ha09011 : a09011.IsHomogeneous 96 := by
  unfold a09011
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09010.pow 1)))

@[irreducible]
def a09012 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a04988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02461 ^ 1)
theorem ha09012 : a09012.IsHomogeneous 96 := by
  unfold a09012
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha04988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02461.pow 1)))

@[irreducible]
def a09013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09012 ^ 1)
theorem ha09013 : a09013.IsHomogeneous 96 := by
  unfold a09013
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09012.pow 1)))

@[irreducible]
def a09014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09011 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09013 ^ 1)
theorem ha09014 : a09014.IsHomogeneous 96 := by
  unfold a09014
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09011.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09013.pow 1)))

@[irreducible]
def a09015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09014 ^ 1) + (C ((144 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09008 ^ 1)
theorem ha09015 : a09015.IsHomogeneous 101 := by
  unfold a09015
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09014.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09008.pow 1)))

@[irreducible]
def a09016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00211 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a00637 ^ 1)
theorem ha09016 : a09016.IsHomogeneous 88 := by
  unfold a09016
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00211.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00139 ^ 1 * a01581 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00465 ^ 1 * a00637 ^ 1)
theorem ha09017 : a09017.IsHomogeneous 88 := by
  unfold a09017
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00139.pow 1)).mul (ha01581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00465.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09016 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a09017 ^ 1)
theorem ha09018 : a09018.IsHomogeneous 88 := by
  unfold a09018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09016.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha09017.pow 1)))

@[irreducible]
def a09019 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02778 ^ 1)
theorem ha09019 : a09019.IsHomogeneous 87 := by
  unfold a09019
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a09020 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a09019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09016 ^ 1)
theorem ha09020 : a09020.IsHomogeneous 88 := by
  unfold a09020
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha09019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09016.pow 1)))

@[irreducible]
def a09021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09018 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09020 ^ 1)
theorem ha09021 : a09021.IsHomogeneous 88 := by
  unfold a09021
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09020.pow 1)))

@[irreducible]
def a09022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09015 ^ 1) + (C ((288 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09021 ^ 1)
theorem ha09022 : a09022.IsHomogeneous 101 := by
  unfold a09022
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09015.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((288 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09021.pow 1)))

@[irreducible]
def a09023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00188 ^ 1 * a00817 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00300 ^ 1 * a00595 ^ 1)
theorem ha09023 : a09023.IsHomogeneous 102 := by
  unfold a09023
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00188.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00300.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a09024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00126 ^ 1 * a01507 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00300 ^ 1 * a00595 ^ 1)
theorem ha09024 : a09024.IsHomogeneous 108 := by
  unfold a09024
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01507.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00300.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a09025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09024 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a09023 ^ 1)
theorem ha09025 : a09025.IsHomogeneous 108 := by
  unfold a09025
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09024.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha09023.pow 1)))

@[irreducible]
def a09026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00188 ^ 1 * a00817 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00046 ^ 1 * a01914 ^ 1)
theorem ha09026 : a09026.IsHomogeneous 94 := by
  unfold a09026
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00188.pow 1)).mul (ha00817.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00046.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a09027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a09026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09023 ^ 1)
theorem ha09027 : a09027.IsHomogeneous 102 := by
  unfold a09027
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha09026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09023.pow 1)))

@[irreducible]
def a09028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09025 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a09027 ^ 1)
theorem ha09028 : a09028.IsHomogeneous 108 := by
  unfold a09028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha09027.pow 1)))

@[irreducible]
def a09029 : Poly := (C ((-15 : ℂ) / (2048 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a09022 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09028 ^ 1)
theorem ha09029 : a09029.IsHomogeneous 108 := by
  unfold a09029
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (2048 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha09022.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09028.pow 1)))

@[irreducible]
def a09030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a02261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04627 ^ 1)
theorem ha09030 : a09030.IsHomogeneous 88 := by
  unfold a09030
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha02261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04627.pow 1)))

@[irreducible]
def a09031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02261 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00963 ^ 1 * a01702 ^ 1)
theorem ha09031 : a09031.IsHomogeneous 87 := by
  unfold a09031
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00963.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09030 ^ 1)
theorem ha09032 : a09032.IsHomogeneous 88 := by
  unfold a09032
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09030.pow 1)))

@[irreducible]
def a09033 : Poly := (C ((-1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02771 ^ 1)
theorem ha09033 : a09033.IsHomogeneous 52 := by
  unfold a09033
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08996.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02771.pow 1)))

@[irreducible]
def a09034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09033 ^ 1) + (C ((1 : ℂ) / (4860 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09003 ^ 1)
theorem ha09034 : a09034.IsHomogeneous 52 := by
  unfold a09034
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09033.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4860 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09003.pow 1)))

@[irreducible]
def a09035 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a04627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09034 ^ 1)
theorem ha09035 : a09035.IsHomogeneous 88 := by
  unfold a09035
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha04627.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09034.pow 1)))

@[irreducible]
def a09036 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a09035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09030 ^ 1)
theorem ha09036 : a09036.IsHomogeneous 88 := by
  unfold a09036
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha09035.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09030.pow 1)))

@[irreducible]
def a09037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09036 ^ 1)
theorem ha09037 : a09037.IsHomogeneous 88 := by
  unfold a09037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09036.pow 1)))

@[irreducible]
def a09038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01067 ^ 1)
theorem ha09038 : a09038.IsHomogeneous 96 := by
  unfold a09038
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02474.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a09039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00379 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01067 ^ 1)
theorem ha09039 : a09039.IsHomogeneous 96 := by
  unfold a09039
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00379.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a09040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09038 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09039 ^ 1)
theorem ha09040 : a09040.IsHomogeneous 96 := by
  unfold a09040
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09038.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09039.pow 1)))

@[irreducible]
def a09041 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a05010 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02474 ^ 1)
theorem ha09041 : a09041.IsHomogeneous 96 := by
  unfold a09041
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha05010.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02474.pow 1)))

@[irreducible]
def a09042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09038 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09041 ^ 1)
theorem ha09042 : a09042.IsHomogeneous 96 := by
  unfold a09042
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09038.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09041.pow 1)))

@[irreducible]
def a09043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09040 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09042 ^ 1)
theorem ha09043 : a09043.IsHomogeneous 96 := by
  unfold a09043
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09042.pow 1)))

@[irreducible]
def a09044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09043 ^ 1) + (C ((648 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09037 ^ 1)
theorem ha09044 : a09044.IsHomogeneous 101 := by
  unfold a09044
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((648 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09037.pow 1)))

@[irreducible]
def a09045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00211 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a00637 ^ 1)
theorem ha09045 : a09045.IsHomogeneous 88 := by
  unfold a09045
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00211.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00141 ^ 1 * a01581 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00469 ^ 1 * a00637 ^ 1)
theorem ha09046 : a09046.IsHomogeneous 88 := by
  unfold a09046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00141.pow 1)).mul (ha01581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00469.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09045 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a09046 ^ 1)
theorem ha09047 : a09047.IsHomogeneous 88 := by
  unfold a09047
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09045.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha09046.pow 1)))

@[irreducible]
def a09048 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02792 ^ 1)
theorem ha09048 : a09048.IsHomogeneous 87 := by
  unfold a09048
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a09049 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a09048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09045 ^ 1)
theorem ha09049 : a09049.IsHomogeneous 88 := by
  unfold a09049
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha09048.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09045.pow 1)))

@[irreducible]
def a09050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09047 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09049 ^ 1)
theorem ha09050 : a09050.IsHomogeneous 88 := by
  unfold a09050
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09047.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09049.pow 1)))

@[irreducible]
def a09051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09044 ^ 1) + (C ((432 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09050 ^ 1)
theorem ha09051 : a09051.IsHomogeneous 101 := by
  unfold a09051
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09044.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09050.pow 1)))

@[irreducible]
def a09052 : Poly := (C ((-5 : ℂ) / (768 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a09051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09028 ^ 1)
theorem ha09052 : a09052.IsHomogeneous 108 := by
  unfold a09052
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (768 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha09051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09028.pow 1)))

@[irreducible]
def a09053 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a09052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09029 ^ 1)
theorem ha09053 : a09053.IsHomogeneous 108 := by
  unfold a09053
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha09052.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09029.pow 1)))

@[irreducible]
def a09054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a02271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04642 ^ 1)
theorem ha09054 : a09054.IsHomogeneous 88 := by
  unfold a09054
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha02271.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04642.pow 1)))

@[irreducible]
def a09055 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a08996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02771 ^ 1)
theorem ha09055 : a09055.IsHomogeneous 52 := by
  unfold a09055
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha08996.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02771.pow 1)))

@[irreducible]
def a09056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09055 ^ 1) + (C ((1 : ℂ) / (1620 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09003 ^ 1)
theorem ha09056 : a09056.IsHomogeneous 52 := by
  unfold a09056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09055.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1620 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09003.pow 1)))

@[irreducible]
def a09057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02777 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a09056 ^ 1)
theorem ha09057 : a09057.IsHomogeneous 52 := by
  unfold a09057
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02777.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha09056.pow 1)))

@[irreducible]
def a09058 : Poly := (C ((-27 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a04642 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09057 ^ 1)
theorem ha09058 : a09058.IsHomogeneous 88 := by
  unfold a09058
  exact ((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha04642.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09057.pow 1)))

@[irreducible]
def a09059 : Poly := (C ((-5 : ℂ) / (27 : ℂ)) * a09058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09054 ^ 1)
theorem ha09059 : a09059.IsHomogeneous 88 := by
  unfold a09059
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (27 : ℂ))).mul (ha09058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09054.pow 1)))

@[irreducible]
def a09060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02271 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00970 ^ 1 * a01702 ^ 1)
theorem ha09060 : a09060.IsHomogeneous 87 := by
  unfold a09060
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02271.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00970.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a09061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a09060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09054 ^ 1)
theorem ha09061 : a09061.IsHomogeneous 88 := by
  unfold a09061
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha09060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09054.pow 1)))

@[irreducible]
def a09062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09061 ^ 1)
theorem ha09062 : a09062.IsHomogeneous 88 := by
  unfold a09062
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09061.pow 1)))

@[irreducible]
def a09063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01074 ^ 1)
theorem ha09063 : a09063.IsHomogeneous 96 := by
  unfold a09063
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a09064 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a05025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02484 ^ 1)
theorem ha09064 : a09064.IsHomogeneous 96 := by
  unfold a09064
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha05025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02484.pow 1)))

@[irreducible]
def a09065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09064 ^ 1)
theorem ha09065 : a09065.IsHomogeneous 96 := by
  unfold a09065
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09064.pow 1)))

@[irreducible]
def a09066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00384 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01074 ^ 1)
theorem ha09066 : a09066.IsHomogeneous 96 := by
  unfold a09066
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00384.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a09067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09066 ^ 1)
theorem ha09067 : a09067.IsHomogeneous 96 := by
  unfold a09067
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09066.pow 1)))

@[irreducible]
def a09068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09065 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09067 ^ 1)
theorem ha09068 : a09068.IsHomogeneous 96 := by
  unfold a09068
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09065.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09067.pow 1)))

@[irreducible]
def a09069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a09068 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09062 ^ 1)
theorem ha09069 : a09069.IsHomogeneous 101 := by
  unfold a09069
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09068.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09062.pow 1)))

@[irreducible]
def a09070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00211 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a00637 ^ 1)
theorem ha09070 : a09070.IsHomogeneous 88 := by
  unfold a09070
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00211.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09071 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02799 ^ 1)
theorem ha09071 : a09071.IsHomogeneous 87 := by
  unfold a09071
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a09072 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a09071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09070 ^ 1)
theorem ha09072 : a09072.IsHomogeneous 88 := by
  unfold a09072
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha09071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09070.pow 1)))

@[irreducible]
def a09073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00144 ^ 1 * a01581 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00473 ^ 1 * a00637 ^ 1)
theorem ha09073 : a09073.IsHomogeneous 88 := by
  unfold a09073
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00144.pow 1)).mul (ha01581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00473.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09070 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a09073 ^ 1)
theorem ha09074 : a09074.IsHomogeneous 88 := by
  unfold a09074
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha09073.pow 1)))

@[irreducible]
def a09075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09074 ^ 1)
theorem ha09075 : a09075.IsHomogeneous 88 := by
  unfold a09075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09074.pow 1)))

@[irreducible]
def a09076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09069 ^ 1) + (C ((216 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09075 ^ 1)
theorem ha09076 : a09076.IsHomogeneous 101 := by
  unfold a09076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09069.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09075.pow 1)))

@[irreducible]
def a09077 : Poly := (C ((-5 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a09076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09028 ^ 1)
theorem ha09077 : a09077.IsHomogeneous 108 := by
  unfold a09077
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha09076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09028.pow 1)))

@[irreducible]
def a09078 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a09077 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09053 ^ 1)
theorem ha09078 : a09078.IsHomogeneous 108 := by
  unfold a09078
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha09077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09053.pow 1)))

@[irreducible]
def a09079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00299 ^ 1 * a04655 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00127 ^ 1 * a09078 ^ 1)
theorem ha09079 : a09079.IsHomogeneous 126 := by
  unfold a09079
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha04655.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00127.pow 1)).mul (ha09078.pow 1)))

@[irreducible]
def a09080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09079 ^ 1)
theorem ha09080 : a09080.IsHomogeneous 126 := by
  unfold a09080
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09079.pow 1)))

@[irreducible]
def a09081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a08987 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09080 ^ 1)
theorem ha09081 : a09081.IsHomogeneous 126 := by
  unfold a09081
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha08987.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09080.pow 1)))

@[irreducible]
def a09082 : Poly := (C ((-1 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a08984 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a09081 ^ 1)
theorem ha09082 : a09082.IsHomogeneous 138 := by
  unfold a09082
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha08984.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha09081.pow 1)))

@[irreducible]
def a09083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a04658 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a09082 ^ 1)
theorem ha09083 : a09083.IsHomogeneous 144 := by
  unfold a09083
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha04658.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha09082.pow 1)))

@[irreducible]
def a09084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a08961 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a09083 ^ 1)
theorem ha09084 : a09084.IsHomogeneous 144 := by
  unfold a09084
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha08961.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha09083.pow 1)))

@[irreducible]
def a09085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a08963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09084 ^ 1)
theorem ha09085 : a09085.IsHomogeneous 144 := by
  unfold a09085
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha08963.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09084.pow 1)))

@[irreducible]
def a09086 : Poly := (C ((-9 : ℂ) / (5120 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 2 * a08960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 4 * a09085 ^ 1)
theorem ha09086 : a09086.IsHomogeneous 168 := by
  unfold a09086
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5120 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha08960.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 4)).mul (ha09085.pow 1)))

@[irreducible]
def a09087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00126 ^ 1 * a09086 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a04661 ^ 1)
theorem ha09087 : a09087.IsHomogeneous 199 := by
  unfold a09087
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00126.pow 1)).mul (ha09086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha04661.pow 1)))

@[irreducible]
def a09088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09087 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a08890 ^ 1)
theorem ha09088 : a09088.IsHomogeneous 199 := by
  unfold a09088
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha08890.pow 1)))

@[irreducible]
def a09089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09088 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a08892 ^ 1)
theorem ha09089 : a09089.IsHomogeneous 199 := by
  unfold a09089
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09088.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha08892.pow 1)))

@[irreducible]
def a09090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09089 ^ 1) + (C ((3 : ℂ) / (800 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 4 * a08889 ^ 1)
theorem ha09090 : a09090.IsHomogeneous 199 := by
  unfold a09090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09089.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (800 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 4)).mul (ha08889.pow 1)))

@[irreducible]
def a09091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01103 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a02540 ^ 1)
theorem ha09091 : a09091.IsHomogeneous 476 := by
  unfold a09091
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01103.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha02540.pow 1)))

@[irreducible]
def a09092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01103 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a02851 ^ 1)
theorem ha09092 : a09092.IsHomogeneous 452 := by
  unfold a09092
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01103.pow 1)).mul (ha01284.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a09093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09091 ^ 1)
theorem ha09093 : a09093.IsHomogeneous 476 := by
  unfold a09093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09091.pow 1)))

@[irreducible]
def a09094 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a02540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a05118 ^ 1)
theorem ha09094 : a09094.IsHomogeneous 500 := by
  unfold a09094
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha02540.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha05118.pow 1)))

@[irreducible]
def a09095 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09091 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09094 ^ 1)
theorem ha09095 : a09095.IsHomogeneous 500 := by
  unfold a09095
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09091.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09094.pow 1)))

@[irreducible]
def a09096 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a09093 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09095 ^ 1)
theorem ha09096 : a09096.IsHomogeneous 500 := by
  unfold a09096
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha09093.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09095.pow 1)))

@[irreducible]
def a09097 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01099 ^ 1 * a01290 ^ 1)
theorem ha09097 : a09097.IsHomogeneous 452 := by
  unfold a09097
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01099.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a09098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a05108 ^ 1)
theorem ha09098 : a09098.IsHomogeneous 392 := by
  unfold a09098
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha02533.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha05108.pow 1)))

@[irreducible]
def a09099 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09098 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09097 ^ 1)
theorem ha09099 : a09099.IsHomogeneous 452 := by
  unfold a09099
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09098.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09097.pow 1)))

@[irreducible]
def a09100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a02860 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01099 ^ 1 * a01290 ^ 1)
theorem ha09100 : a09100.IsHomogeneous 476 := by
  unfold a09100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha02860.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01099.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a09101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09100 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09097 ^ 1)
theorem ha09101 : a09101.IsHomogeneous 476 := by
  unfold a09101
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09100.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09097.pow 1)))

@[irreducible]
def a09102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09101 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09099 ^ 1)
theorem ha09102 : a09102.IsHomogeneous 476 := by
  unfold a09102
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09101.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09099.pow 1)))

@[irreducible]
def a09103 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a04706 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a02304 ^ 1)
theorem ha09103 : a09103.IsHomogeneous 376 := by
  unfold a09103
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha04706.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha02304.pow 1)))

@[irreducible]
def a09104 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00487 ^ 1 * a00506 ^ 1)
theorem ha09104 : a09104.IsHomogeneous 97 := by
  unfold a09104
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a09105 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00487 ^ 1 * a00506 ^ 1)
theorem ha09105 : a09105.IsHomogeneous 133 := by
  unfold a09105
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha01281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00487.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a09106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a09104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09105 ^ 1)
theorem ha09106 : a09106.IsHomogeneous 133 := by
  unfold a09106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha09104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09105.pow 1)))

@[irreducible]
def a09107 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01281 ^ 1)
theorem ha09107 : a09107.IsHomogeneous 133 := by
  unfold a09107
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha02847.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a09108 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a09107 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09105 ^ 1)
theorem ha09108 : a09108.IsHomogeneous 133 := by
  unfold a09108
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha09107.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09105.pow 1)))

@[irreducible]
def a09109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09108 ^ 1)
theorem ha09109 : a09109.IsHomogeneous 133 := by
  unfold a09109
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09108.pow 1)))

@[irreducible]
def a09110 : Poly := (C ((-5 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a09109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a02825 ^ 1)
theorem ha09110 : a09110.IsHomogeneous 145 := by
  unfold a09110
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha09109.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02825.pow 1)))

@[irreducible]
def a09111 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02530 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01097 ^ 1)
theorem ha09111 : a09111.IsHomogeneous 139 := by
  unfold a09111
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02530.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a09112 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00395 ^ 1 * a00864 ^ 1)
theorem ha09112 : a09112.IsHomogeneous 139 := by
  unfold a09112
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01097.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00395.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a09113 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a09112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09111 ^ 1)
theorem ha09113 : a09113.IsHomogeneous 139 := by
  unfold a09113
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha09112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09111.pow 1)))

@[irreducible]
def a09114 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a05104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02530 ^ 1)
theorem ha09114 : a09114.IsHomogeneous 145 := by
  unfold a09114
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha05104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02530.pow 1)))

@[irreducible]
def a09115 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09111 ^ 1)
theorem ha09115 : a09115.IsHomogeneous 145 := by
  unfold a09115
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09114.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09111.pow 1)))

@[irreducible]
def a09116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a09113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09115 ^ 1)
theorem ha09116 : a09116.IsHomogeneous 145 := by
  unfold a09116
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha09113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09115.pow 1)))

@[irreducible]
def a09117 : Poly := (C ((-125 : ℂ) / (1296 : ℂ)) * a09116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09110 ^ 1)
theorem ha09117 : a09117.IsHomogeneous 145 := by
  unfold a09117
  exact (((isHomogeneous_C (σ := Fin 6) ((-125 : ℂ) / (1296 : ℂ))).mul (ha09116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09110.pow 1)))

@[irreducible]
def a09118 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a02302 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a04703 ^ 1)
theorem ha09118 : a09118.IsHomogeneous 169 := by
  unfold a09118
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha02302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha04703.pow 1)))

@[irreducible]
def a09119 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a00985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a02302 ^ 1)
theorem ha09119 : a09119.IsHomogeneous 163 := by
  unfold a09119
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha00985.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha02302.pow 1)))

@[irreducible]
def a09120 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a09119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09118 ^ 1)
theorem ha09120 : a09120.IsHomogeneous 169 := by
  unfold a09120
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha09119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09118.pow 1)))

@[irreducible]
def a09121 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00260 ^ 1 * a04689 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a02295 ^ 1)
theorem ha09121 : a09121.IsHomogeneous 141 := by
  unfold a09121
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00260.pow 1)).mul (ha04689.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a09122 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00982 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02295 ^ 1)
theorem ha09122 : a09122.IsHomogeneous 138 := by
  unfold a09122
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00982.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02295.pow 1)))

@[irreducible]
def a09123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09121 ^ 1)
theorem ha09123 : a09123.IsHomogeneous 141 := by
  unfold a09123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09122.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09121.pow 1)))

@[irreducible]
def a09124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00188 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00260 ^ 1 * a00595 ^ 1)
theorem ha09124 : a09124.IsHomogeneous 90 := by
  unfold a09124
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00188.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00260.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a09125 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00260 ^ 1 * a00595 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01507 ^ 1)
theorem ha09125 : a09125.IsHomogeneous 90 := by
  unfold a09125
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00260.pow 1)).mul (ha00595.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01507.pow 1)))

@[irreducible]
def a09126 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a09125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09124 ^ 1)
theorem ha09126 : a09126.IsHomogeneous 90 := by
  unfold a09126
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha09125.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09124.pow 1)))

@[irreducible]
def a09127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a01702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00712 ^ 1)
theorem ha09127 : a09127.IsHomogeneous 88 := by
  unfold a09127
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a09128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a09127 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a09124 ^ 1)
theorem ha09128 : a09128.IsHomogeneous 90 := by
  unfold a09128
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha09127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha09124.pow 1)))

@[irreducible]
def a09129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09126 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a09128 ^ 1)
theorem ha09129 : a09129.IsHomogeneous 90 := by
  unfold a09129
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha09128.pow 1)))

@[irreducible]
def a09130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00637 ^ 1)
theorem ha09130 : a09130.IsHomogeneous 101 := by
  unfold a09130
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a09131 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01581 ^ 1)
theorem ha09131 : a09131.IsHomogeneous 101 := by
  unfold a09131
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09132 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a09131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09130 ^ 1)
theorem ha09132 : a09132.IsHomogeneous 101 := by
  unfold a09132
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha09131.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09130.pow 1)))

@[irreducible]
def a09133 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00061 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00691 ^ 1)
theorem ha09133 : a09133.IsHomogeneous 101 := by
  unfold a09133
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a09134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09133 ^ 1)
theorem ha09134 : a09134.IsHomogeneous 101 := by
  unfold a09134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09133.pow 1)))

@[irreducible]
def a09135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09132 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09134 ^ 1)
theorem ha09135 : a09135.IsHomogeneous 101 := by
  unfold a09135
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09132.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09134.pow 1)))

@[irreducible]
def a09136 : Poly := (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a09135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09129 ^ 1)
theorem ha09136 : a09136.IsHomogeneous 104 := by
  unfold a09136
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha09135.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09129.pow 1)))

@[irreducible]
def a09137 : Poly := (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a09135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09136 ^ 1)
theorem ha09137 : a09137.IsHomogeneous 104 := by
  unfold a09137
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha09135.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09136.pow 1)))

@[irreducible]
def a09138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09137 ^ 1)
theorem ha09138 : a09138.IsHomogeneous 104 := by
  unfold a09138
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09137.pow 1)))

@[irreducible]
def a09139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a09138 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00260 ^ 1 * a04689 ^ 1)
theorem ha09139 : a09139.IsHomogeneous 141 := by
  unfold a09139
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha09138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00260.pow 1)).mul (ha04689.pow 1)))

@[irreducible]
def a09140 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a09139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09121 ^ 1)
theorem ha09140 : a09140.IsHomogeneous 141 := by
  unfold a09140
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha09139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09121.pow 1)))

@[irreducible]
def a09141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09140 ^ 1)
theorem ha09141 : a09141.IsHomogeneous 141 := by
  unfold a09141
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09123.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09140.pow 1)))

@[irreducible]
def a09142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00691 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02520 ^ 1)
theorem ha09142 : a09142.IsHomogeneous 152 := by
  unfold a09142
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00691.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09143 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00393 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a01092 ^ 1)
theorem ha09143 : a09143.IsHomogeneous 150 := by
  unfold a09143
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00393.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a09144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a09143 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09142 ^ 1)
theorem ha09144 : a09144.IsHomogeneous 152 := by
  unfold a09144
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha09143.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09142.pow 1)))

@[irreducible]
def a09145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00241 ^ 1 * a02520 ^ 1)
theorem ha09145 : a09145.IsHomogeneous 152 := by
  unfold a09145
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00241.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a09146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09142 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a09145 ^ 1)
theorem ha09146 : a09146.IsHomogeneous 152 := by
  unfold a09146
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha09145.pow 1)))

@[irreducible]
def a09147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09146 ^ 1)
theorem ha09147 : a09147.IsHomogeneous 152 := by
  unfold a09147
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09146.pow 1)))

@[irreducible]
def a09148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a09141 ^ 1) + (C ((125 : ℂ) / (5184 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a09147 ^ 1)
theorem ha09148 : a09148.IsHomogeneous 154 := by
  unfold a09148
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha09141.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (5184 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha09147.pow 1)))

@[irreducible]
def a09149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00484 ^ 1 * a00637 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00211 ^ 1 * a01275 ^ 1)
theorem ha09149 : a09149.IsHomogeneous 139 := by
  unfold a09149
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00484.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00211.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a09150 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00484 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a01581 ^ 1)
theorem ha09150 : a09150.IsHomogeneous 137 := by
  unfold a09150
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00484.pow 1)).mul (ha00637.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a09151 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a09150 ^ 1)
theorem ha09151 : a09151.IsHomogeneous 139 := by
  unfold a09151
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09149.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha09150.pow 1)))

@[irreducible]
def a09152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00061 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a01275 ^ 1)
theorem ha09152 : a09152.IsHomogeneous 139 := by
  unfold a09152
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00061.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a09153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09149 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a09152 ^ 1)
theorem ha09153 : a09153.IsHomogeneous 139 := by
  unfold a09153
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha09152.pow 1)))

@[irreducible]
def a09154 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a09153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09151 ^ 1)
theorem ha09154 : a09154.IsHomogeneous 139 := by
  unfold a09154
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha09153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09151.pow 1)))

@[irreducible]
def a09155 : Poly := (C ((-25 : ℂ) / (108 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a09154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09148 ^ 1)
theorem ha09155 : a09155.IsHomogeneous 154 := by
  unfold a09155
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (108 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha09154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09148.pow 1)))

@[irreducible]
def a09156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00595 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00188 ^ 1 * a00829 ^ 1)
theorem ha09156 : a09156.IsHomogeneous 127 := by
  unfold a09156
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00595.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00188.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a09157 : Poly := (C ((-4 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01507 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00595 ^ 1)
theorem ha09157 : a09157.IsHomogeneous 90 := by
  unfold a09157
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01507.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00595.pow 1)))

@[irreducible]
def a09158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a09157 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09156 ^ 1)
theorem ha09158 : a09158.IsHomogeneous 127 := by
  unfold a09158
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha09157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09156.pow 1)))

@[irreducible]
def a09159 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00188 ^ 1 * a00829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00046 ^ 1 * a01938 ^ 1)
theorem ha09159 : a09159.IsHomogeneous 127 := by
  unfold a09159
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00188.pow 1)).mul (ha00829.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00046.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a09160 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a09159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09156 ^ 1)
theorem ha09160 : a09160.IsHomogeneous 127 := by
  unfold a09160
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha09159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09156.pow 1)))

@[irreducible]
def a09161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09160 ^ 1)
theorem ha09161 : a09161.IsHomogeneous 127 := by
  unfold a09161
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09160.pow 1)))

@[irreducible]
def a09162 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a09161 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09155 ^ 1)
theorem ha09162 : a09162.IsHomogeneous 154 := by
  unfold a09162
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha09161.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09155.pow 1)))

@[irreducible]
def a09163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a04703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a09162 ^ 1)
theorem ha09163 : a09163.IsHomogeneous 178 := by
  unfold a09163
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha04703.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha09162.pow 1)))

@[irreducible]
def a09164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a09118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09163 ^ 1)
theorem ha09164 : a09164.IsHomogeneous 178 := by
  unfold a09164
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha09118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09163.pow 1)))

@[irreducible]
def a09165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a09120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09164 ^ 1)
theorem ha09165 : a09165.IsHomogeneous 178 := by
  unfold a09165
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha09120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09164.pow 1)))

@[irreducible]
def a09166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09165 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a09117 ^ 1)
theorem ha09166 : a09166.IsHomogeneous 178 := by
  unfold a09166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09165.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha09117.pow 1)))

@[irreducible]
def a09167 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a09166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a04706 ^ 1)
theorem ha09167 : a09167.IsHomogeneous 286 := by
  unfold a09167
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha09166.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha04706.pow 1)))

@[irreducible]
def a09168 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a09167 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09103 ^ 1)
theorem ha09168 : a09168.IsHomogeneous 376 := by
  unfold a09168
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha09167.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09103.pow 1)))

@[irreducible]
def a09169 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00986 ^ 1 * a01949 ^ 1)
theorem ha09169 : a09169.IsHomogeneous 436 := by
  unfold a09169
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00986.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a09170 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09103 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09169 ^ 1)
theorem ha09170 : a09170.IsHomogeneous 436 := by
  unfold a09170
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09103.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09169.pow 1)))

@[irreducible]
def a09171 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a09168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09170 ^ 1)
theorem ha09171 : a09171.IsHomogeneous 436 := by
  unfold a09171
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha09168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09170.pow 1)))

@[irreducible]
def a09172 : Poly := (C ((-25 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00042 ^ 1 * a09102 ^ 1) + (C ((-25 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a09096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a09171 ^ 1)
theorem ha09172 : a09172.IsHomogeneous 502 := by
  unfold a09172
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00042.pow 1)).mul (ha09102.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha09096.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha09171.pow 1)))

@[irreducible]
def a09173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09172 ^ 1) + (C ((50 : ℂ) / (243 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a09090 ^ 1)
theorem ha09173 : a09173.IsHomogeneous 502 := by
  unfold a09173
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09172.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (243 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha09090.pow 1)))

@[irreducible]
def a09174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a04711 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a09173 ^ 1)
theorem ha09174 : a09174.IsHomogeneous 502 := by
  unfold a09174
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha04711.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha09173.pow 1)))

@[irreducible]
def a09175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09174 ^ 1)
theorem ha09175 : a09175.IsHomogeneous 502 := by
  unfold a09175
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08873.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09174.pow 1)))

@[irreducible]
def a09176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08875 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09175 ^ 1)
theorem ha09176 : a09176.IsHomogeneous 502 := by
  unfold a09176
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08875.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09175.pow 1)))

@[irreducible]
def a09177 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a04713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a09176 ^ 1)
theorem ha09177 : a09177.IsHomogeneous 928 := by
  unfold a09177
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha04713.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha09176.pow 1)))

@[irreducible]
def a09178 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a08870 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09177 ^ 1)
theorem ha09178 : a09178.IsHomogeneous 1261 := by
  unfold a09178
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha08870.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09177.pow 1)))

@[irreducible]
def a09179 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a08872 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09178 ^ 1)
theorem ha09179 : a09179.IsHomogeneous 1594 := by
  unfold a09179
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha08872.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09178.pow 1)))

@[irreducible]
def a09180 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a02327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a04754 ^ 1)
theorem ha09180 : a09180.IsHomogeneous 1105 := by
  unfold a09180
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02327.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha04754.pow 1)))

@[irreducible]
def a09181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02327 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00996 ^ 1 * a01886 ^ 1)
theorem ha09181 : a09181.IsHomogeneous 1402 := by
  unfold a09181
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00996.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a09182 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a09181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a09180 ^ 1)
theorem ha09182 : a09182.IsHomogeneous 1438 := by
  unfold a09182
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha09181.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha09180.pow 1)))

@[irreducible]
def a09183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04752 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02326 ^ 1)
theorem ha09183 : a09183.IsHomogeneous 346 := by
  unfold a09183
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04752.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02326.pow 1)))

@[irreducible]
def a09184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a02326 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00996 ^ 1 * a01976 ^ 1)
theorem ha09184 : a09184.IsHomogeneous 346 := by
  unfold a09184
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha02326.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00996.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a09185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09184 ^ 1)
theorem ha09185 : a09185.IsHomogeneous 346 := by
  unfold a09185
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09184.pow 1)))

@[irreducible]
def a09186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a02320 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04738 ^ 1)
theorem ha09186 : a09186.IsHomogeneous 90 := by
  unfold a09186
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha02320.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04738.pow 1)))

@[irreducible]
def a09187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a02313 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a04724 ^ 1)
theorem ha09187 : a09187.IsHomogeneous 69 := by
  unfold a09187
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha02313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha04724.pow 1)))

@[irreducible]
def a09188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a02313 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00991 ^ 1 * a01903 ^ 1)
theorem ha09188 : a09188.IsHomogeneous 63 := by
  unfold a09188
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha02313.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00991.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a09189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09187 ^ 1)
theorem ha09189 : a09189.IsHomogeneous 69 := by
  unfold a09189
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09188.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09187.pow 1)))

@[irreducible]
def a09190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01041 ^ 1 * a01207 ^ 1)
theorem ha09190 : a09190.IsHomogeneous 30 := by
  unfold a09190
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02413.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01041.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a09191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a04894 ^ 1)
theorem ha09191 : a09191.IsHomogeneous 30 := by
  unfold a09191
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha02413.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a09192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09191 ^ 1)
theorem ha09192 : a09192.IsHomogeneous 30 := by
  unfold a09192
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09191.pow 1)))

@[irreducible]
def a09193 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a01041 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a02710 ^ 1)
theorem ha09193 : a09193.IsHomogeneous 24 := by
  unfold a09193
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha01041.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a09194 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09193 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09190 ^ 1)
theorem ha09194 : a09194.IsHomogeneous 30 := by
  unfold a09194
  exact ((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09193.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09190.pow 1)))

@[irreducible]
def a09195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09192 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09194 ^ 1)
theorem ha09195 : a09195.IsHomogeneous 30 := by
  unfold a09195
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09192.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09194.pow 1)))

@[irreducible]
def a09196 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09195 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02879 ^ 1)
theorem ha09196 : a09196.IsHomogeneous 58 := by
  unfold a09196
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09195.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a09197 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a09195 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09196 ^ 1)
theorem ha09197 : a09197.IsHomogeneous 58 := by
  unfold a09197
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha09195.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09196.pow 1)))

@[irreducible]
def a09198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a02879 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09197 ^ 1)
theorem ha09198 : a09198.IsHomogeneous 58 := by
  unfold a09198
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha02879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09197.pow 1)))

@[irreducible]
def a09199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a09198 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00299 ^ 1 * a04724 ^ 1)
theorem ha09199 : a09199.IsHomogeneous 76 := by
  unfold a09199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha09198.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha04724.pow 1)))

@[irreducible]
def a09200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09199 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09187 ^ 1)
theorem ha09200 : a09200.IsHomogeneous 76 := by
  unfold a09200
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09199.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09187.pow 1)))

@[irreducible]
def a09201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09200 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a09189 ^ 1)
theorem ha09201 : a09201.IsHomogeneous 76 := by
  unfold a09201
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09200.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha09189.pow 1)))

@[irreducible]
def a09202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01107 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a02551 ^ 1)
theorem ha09202 : a09202.IsHomogeneous 70 := by
  unfold a09202
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01107.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a09203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01107 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00400 ^ 1 * a02754 ^ 1)
theorem ha09203 : a09203.IsHomogeneous 64 := by
  unfold a09203
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01107.pow 1)).mul (ha01228.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a09204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09202 ^ 1)
theorem ha09204 : a09204.IsHomogeneous 70 := by
  unfold a09204
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09202.pow 1)))

@[irreducible]
def a09205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a05141 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00461 ^ 1 * a02551 ^ 1)
theorem ha09205 : a09205.IsHomogeneous 71 := by
  unfold a09205
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha05141.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00461.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a09206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09205 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a09202 ^ 1)
theorem ha09206 : a09206.IsHomogeneous 71 := by
  unfold a09206
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09205.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha09202.pow 1)))

@[irreducible]
def a09207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09206 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a09204 ^ 1)
theorem ha09207 : a09207.IsHomogeneous 71 := by
  unfold a09207
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09206.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha09204.pow 1)))

@[irreducible]
def a09208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a09201 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a09207 ^ 1)
theorem ha09208 : a09208.IsHomogeneous 82 := by
  unfold a09208
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha09201.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha09207.pow 1)))

@[irreducible]
def a09209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00494 ^ 1 * a02441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01052 ^ 1 * a01298 ^ 1)
theorem ha09209 : a09209.IsHomogeneous 65 := by
  unfold a09209
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha02441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01052.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a09210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a02441 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a04950 ^ 1)
theorem ha09210 : a09210.IsHomogeneous 59 := by
  unfold a09210
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha02441.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha04950.pow 1)))

@[irreducible]
def a09211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09209 ^ 1)
theorem ha09211 : a09211.IsHomogeneous 65 := by
  unfold a09211
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09210.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09209.pow 1)))

@[irreducible]
def a09212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01052 ^ 1 * a01298 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a00372 ^ 1 * a02879 ^ 1)
theorem ha09212 : a09212.IsHomogeneous 71 := by
  unfold a09212
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01052.pow 1)).mul (ha01298.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a09213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09212 ^ 1)
theorem ha09213 : a09213.IsHomogeneous 71 := by
  unfold a09213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09212.pow 1)))

@[irreducible]
def a09214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09213 ^ 1)
theorem ha09214 : a09214.IsHomogeneous 71 := by
  unfold a09214
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09211.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09213.pow 1)))

@[irreducible]
def a09215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09208 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a09214 ^ 1)
theorem ha09215 : a09215.IsHomogeneous 82 := by
  unfold a09215
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09208.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha09214.pow 1)))

end CycleQ2Concrete
