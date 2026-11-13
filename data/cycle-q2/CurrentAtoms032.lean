import Proposal.CurrentAtoms031

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a09984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00506 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1)
theorem ha09984 : a09984.IsHomogeneous 42 := by
  unfold a09984
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a09985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09982 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a09984 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a09983 ^ 1)
theorem ha09985 : a09985.IsHomogeneous 42 := by
  unfold a09985
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha09984.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha09983.pow 1)))

@[irreducible]
def a09986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00298 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00506 ^ 1 * a00809 ^ 1)
theorem ha09986 : a09986.IsHomogeneous 42 := by
  unfold a09986
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00298.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00506.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a09987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01896 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00809 ^ 1)
theorem ha09987 : a09987.IsHomogeneous 39 := by
  unfold a09987
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a09988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09982 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09987 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a09986 ^ 1)
theorem ha09988 : a09988.IsHomogeneous 42 := by
  unfold a09988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09987.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha09986.pow 1)))

@[irreducible]
def a09989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a01327 ^ 1)
theorem ha09989 : a09989.IsHomogeneous 36 := by
  unfold a09989
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02935.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a09990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09983 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a09989 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a09986 ^ 1)
theorem ha09990 : a09990.IsHomogeneous 42 := by
  unfold a09990
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09983.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha09989.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha09986.pow 1)))

@[irreducible]
def a09991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09988 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a09990 ^ 1)
theorem ha09991 : a09991.IsHomogeneous 42 := by
  unfold a09991
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09988.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha09990.pow 1)))

@[irreducible]
def a09992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00809 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01896 ^ 1)
theorem ha09992 : a09992.IsHomogeneous 33 := by
  unfold a09992
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a09993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha09993 : a09993.IsHomogeneous 36 := by
  unfold a09993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a09994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09993 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09982 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a09992 ^ 1)
theorem ha09994 : a09994.IsHomogeneous 42 := by
  unfold a09994
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09982.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha09992.pow 1)))

@[irreducible]
def a09995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha09995 : a09995.IsHomogeneous 36 := by
  unfold a09995
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a09996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09993 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a09995 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a09984 ^ 1)
theorem ha09996 : a09996.IsHomogeneous 42 := by
  unfold a09996
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09993.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha09995.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha09984.pow 1)))

@[irreducible]
def a09997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09996 ^ 1)
theorem ha09997 : a09997.IsHomogeneous 42 := by
  unfold a09997
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09994.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09996.pow 1)))

@[irreducible]
def a09998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01896 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03890 ^ 1)
theorem ha09998 : a09998.IsHomogeneous 33 := by
  unfold a09998
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a09999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a09998 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09987 ^ 1)
theorem ha09999 : a09999.IsHomogeneous 39 := by
  unfold a09999
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09992.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha09998.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09987.pow 1)))

@[irreducible]
def a10000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09994 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a09999 ^ 1)
theorem ha10000 : a10000.IsHomogeneous 42 := by
  unfold a10000
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09988.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09994.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha09999.pow 1)))

@[irreducible]
def a10001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09997 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10000 ^ 1)
theorem ha10001 : a10001.IsHomogeneous 42 := by
  unfold a10001
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09997.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10000.pow 1)))

@[irreducible]
def a10002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a09979 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a10001 ^ 1)
theorem ha10002 : a10002.IsHomogeneous 49 := by
  unfold a10002
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha09979.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha10001.pow 1)))

@[irreducible]
def a10003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09980 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10002 ^ 1)
theorem ha10003 : a10003.IsHomogeneous 49 := by
  unfold a10003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09980.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10002.pow 1)))

@[irreducible]
def a10004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09981 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10003 ^ 1)
theorem ha10004 : a10004.IsHomogeneous 49 := by
  unfold a10004
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10003.pow 1)))

@[irreducible]
def a10005 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a09959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a09981 ^ 1)
theorem ha10005 : a10005.IsHomogeneous 49 := by
  unfold a10005
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha09959.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09981.pow 1)))

@[irreducible]
def a10006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10005 ^ 1)
theorem ha10006 : a10006.IsHomogeneous 49 := by
  unfold a10006
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10005.pow 1)))

@[irreducible]
def a10007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10002 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a10001 ^ 1)
theorem ha10007 : a10007.IsHomogeneous 49 := by
  unfold a10007
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10002.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha10001.pow 1)))

@[irreducible]
def a10008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10003 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10007 ^ 1)
theorem ha10008 : a10008.IsHomogeneous 49 := by
  unfold a10008
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10007.pow 1)))

@[irreducible]
def a10009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10008 ^ 1)
theorem ha10009 : a10009.IsHomogeneous 49 := by
  unfold a10009
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10008.pow 1)))

@[irreducible]
def a10010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10009 ^ 1)
theorem ha10010 : a10010.IsHomogeneous 49 := by
  unfold a10010
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10009.pow 1)))

@[irreducible]
def a10011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a06060 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06461 ^ 1)
theorem ha10011 : a10011.IsHomogeneous 50 := by
  unfold a10011
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha06060.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06461.pow 1)))

@[irreducible]
def a10012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a06060 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06444 ^ 1)
theorem ha10012 : a10012.IsHomogeneous 50 := by
  unfold a10012
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha06060.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06444.pow 1)))

@[irreducible]
def a10013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10011 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10012 ^ 1)
theorem ha10013 : a10013.IsHomogeneous 50 := by
  unfold a10013
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10011.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10012.pow 1)))

@[irreducible]
def a10014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10012 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06444 ^ 1)
theorem ha10014 : a10014.IsHomogeneous 50 := by
  unfold a10014
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10012.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06444.pow 1)))

@[irreducible]
def a10015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10014 ^ 1)
theorem ha10015 : a10015.IsHomogeneous 50 := by
  unfold a10015
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10014.pow 1)))

@[irreducible]
def a10016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10011 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06461 ^ 1)
theorem ha10016 : a10016.IsHomogeneous 50 := by
  unfold a10016
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10011.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06461.pow 1)))

@[irreducible]
def a10017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10016 ^ 1)
theorem ha10017 : a10017.IsHomogeneous 50 := by
  unfold a10017
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10016.pow 1)))

@[irreducible]
def a10018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10015 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10017 ^ 1)
theorem ha10018 : a10018.IsHomogeneous 50 := by
  unfold a10018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10015.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10017.pow 1)))

@[irreducible]
def a10019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10014 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06444 ^ 1)
theorem ha10019 : a10019.IsHomogeneous 50 := by
  unfold a10019
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10014.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06444.pow 1)))

@[irreducible]
def a10020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10015 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10019 ^ 1)
theorem ha10020 : a10020.IsHomogeneous 50 := by
  unfold a10020
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10015.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10019.pow 1)))

@[irreducible]
def a10021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10018 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10020 ^ 1)
theorem ha10021 : a10021.IsHomogeneous 50 := by
  unfold a10021
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10020.pow 1)))

@[irreducible]
def a10022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05809 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06559 ^ 1)
theorem ha10022 : a10022.IsHomogeneous 50 := by
  unfold a10022
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05809.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06559.pow 1)))

@[irreducible]
def a10023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10022 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06559 ^ 1)
theorem ha10023 : a10023.IsHomogeneous 50 := by
  unfold a10023
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05809.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10022.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06559.pow 1)))

@[irreducible]
def a10024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10022 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06559 ^ 1)
theorem ha10024 : a10024.IsHomogeneous 50 := by
  unfold a10024
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10022.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06559.pow 1)))

@[irreducible]
def a10025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06559 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10024 ^ 1)
theorem ha10025 : a10025.IsHomogeneous 50 := by
  unfold a10025
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06559.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10023.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10024.pow 1)))

@[irreducible]
def a10026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05809 ^ 1)
theorem ha10026 : a10026.IsHomogeneous 50 := by
  unfold a10026
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06596.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05809.pow 1)))

@[irreducible]
def a10027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10022 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10026 ^ 1)
theorem ha10027 : a10027.IsHomogeneous 50 := by
  unfold a10027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10022.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10026.pow 1)))

@[irreducible]
def a10028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a05809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10026 ^ 1)
theorem ha10028 : a10028.IsHomogeneous 50 := by
  unfold a10028
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06596.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha05809.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10026.pow 1)))

@[irreducible]
def a10029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10027 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10028 ^ 1)
theorem ha10029 : a10029.IsHomogeneous 50 := by
  unfold a10029
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10027.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10028.pow 1)))

@[irreducible]
def a10030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10027 ^ 1)
theorem ha10030 : a10030.IsHomogeneous 50 := by
  unfold a10030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10027.pow 1)))

@[irreducible]
def a10031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10029 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10030 ^ 1)
theorem ha10031 : a10031.IsHomogeneous 50 := by
  unfold a10031
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10029.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10030.pow 1)))

@[irreducible]
def a10032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06596 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10026 ^ 1)
theorem ha10032 : a10032.IsHomogeneous 50 := by
  unfold a10032
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06596.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10026.pow 1)))

@[irreducible]
def a10033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10027 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10032 ^ 1)
theorem ha10033 : a10033.IsHomogeneous 50 := by
  unfold a10033
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10027.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10032.pow 1)))

@[irreducible]
def a10034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10032 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a06596 ^ 1)
theorem ha10034 : a10034.IsHomogeneous 50 := by
  unfold a10034
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10032.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha06596.pow 1)))

@[irreducible]
def a10035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10029 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10034 ^ 1)
theorem ha10035 : a10035.IsHomogeneous 50 := by
  unfold a10035
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10029.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10033.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10034.pow 1)))

@[irreducible]
def a10036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10030 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10033 ^ 1)
theorem ha10036 : a10036.IsHomogeneous 50 := by
  unfold a10036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10030.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10033.pow 1)))

@[irreducible]
def a10037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10036 ^ 1)
theorem ha10037 : a10037.IsHomogeneous 50 := by
  unfold a10037
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10035.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10036.pow 1)))

@[irreducible]
def a10038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00317 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00510 ^ 1 * a00632 ^ 1)
theorem ha10038 : a10038.IsHomogeneous 39 := by
  unfold a10038
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a10039 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00317 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1 * a01335 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00510 ^ 1 * a00865 ^ 1)
theorem ha10039 : a10039.IsHomogeneous 39 := by
  unfold a10039
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha01335.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00510.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a10040 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1 * a02949 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00058 ^ 1 * a00317 ^ 1 * a01335 ^ 1)
theorem ha10040 : a10040.IsHomogeneous 39 := by
  unfold a10040
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha02949.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a10041 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a10039 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a10040 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10038 ^ 1)
theorem ha10041 : a10041.IsHomogeneous 39 := by
  unfold a10041
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha10039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha10040.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10038.pow 1)))

@[irreducible]
def a10042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00632 ^ 1 * a01335 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00510 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00510 ^ 1 * a01575 ^ 1)
theorem ha10042 : a10042.IsHomogeneous 42 := by
  unfold a10042
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1)).mul (ha01335.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00510.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a10043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a02949 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00632 ^ 1 * a01335 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1 * a01335 ^ 1)
theorem ha10043 : a10043.IsHomogeneous 42 := by
  unfold a10043
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha02949.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1)).mul (ha01335.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a10044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10042 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a10043 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10038 ^ 1)
theorem ha10044 : a10044.IsHomogeneous 42 := by
  unfold a10044
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha10043.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10038.pow 1)))

@[irreducible]
def a10045 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a02949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1 * a05775 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1 * a02949 ^ 1)
theorem ha10045 : a10045.IsHomogeneous 42 := by
  unfold a10045
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha02949.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha05775.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a10046 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a10040 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a10045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10043 ^ 1)
theorem ha10046 : a10046.IsHomogeneous 42 := by
  unfold a10046
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha10040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha10045.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10043.pow 1)))

@[irreducible]
def a10047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10044 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a10046 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a10041 ^ 1)
theorem ha10047 : a10047.IsHomogeneous 42 := by
  unfold a10047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha10046.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha10041.pow 1)))

@[irreducible]
def a10048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00317 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00317 ^ 1 * a00632 ^ 1)
theorem ha10048 : a10048.IsHomogeneous 45 := by
  unfold a10048
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a10049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00317 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00510 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a01575 ^ 1)
theorem ha10049 : a10049.IsHomogeneous 45 := by
  unfold a10049
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00317.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a10050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10048 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10038 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a10049 ^ 1)
theorem ha10050 : a10050.IsHomogeneous 45 := by
  unfold a10050
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10038.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha10049.pow 1)))

@[irreducible]
def a10051 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00058 ^ 1 * a00156 ^ 1 * a02008 ^ 1) + (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00510 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1 * a00865 ^ 1)
theorem ha10051 : a10051.IsHomogeneous 45 := by
  unfold a10051
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha02008.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00510.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a10052 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 6 * a10039 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10051 ^ 1)
theorem ha10052 : a10052.IsHomogeneous 45 := by
  unfold a10052
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 6)).mul (ha10039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10048.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10051.pow 1)))

@[irreducible]
def a10053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10050 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10052 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a10041 ^ 1)
theorem ha10053 : a10053.IsHomogeneous 45 := by
  unfold a10053
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10050.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10052.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha10041.pow 1)))

@[irreducible]
def a10054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00510 ^ 1 * a01575 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a01575 ^ 1)
theorem ha10054 : a10054.IsHomogeneous 42 := by
  unfold a10054
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00510.pow 1)).mul (ha01575.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a10055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10049 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a10042 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a10054 ^ 1)
theorem ha10055 : a10055.IsHomogeneous 45 := by
  unfold a10055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10049.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha10042.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha10054.pow 1)))

@[irreducible]
def a10056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10050 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a10055 ^ 1) + (C ((7 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a10044 ^ 1)
theorem ha10056 : a10056.IsHomogeneous 45 := by
  unfold a10056
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10050.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha10055.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha10044.pow 1)))

@[irreducible]
def a10057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10056 ^ 1) + (C ((7 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a10047 ^ 1)
theorem ha10057 : a10057.IsHomogeneous 45 := by
  unfold a10057
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10056.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha10047.pow 1)))

@[irreducible]
def a10058 : Poly := (C ((-32 : ℂ) / (7 : ℂ)) * a10057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06637 ^ 1)
theorem ha10058 : a10058.IsHomogeneous 45 := by
  unfold a10058
  exact (((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (7 : ℂ))).mul (ha10057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06637.pow 1)))

@[irreducible]
def a10059 : Poly := (C ((-32 : ℂ) / (7 : ℂ)) * a10057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06637 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10058 ^ 1)
theorem ha10059 : a10059.IsHomogeneous 45 := by
  unfold a10059
  exact ((((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (7 : ℂ))).mul (ha10057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06637.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10058.pow 1)))

@[irreducible]
def a10060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10057 ^ 1) + (C ((7 : ℂ) / (19440 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1)
theorem ha10060 : a10060.IsHomogeneous 45 := by
  unfold a10060
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10057.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (19440 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)))

@[irreducible]
def a10061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10057 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10060 ^ 1) + (C ((7 : ℂ) / (19440 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1)
theorem ha10061 : a10061.IsHomogeneous 45 := by
  unfold a10061
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10060.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (19440 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)))

@[irreducible]
def a10062 : Poly := (C ((-2 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06637 ^ 1)
theorem ha10062 : a10062.IsHomogeneous 45 := by
  unfold a10062
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06637.pow 1)))

@[irreducible]
def a10063 : Poly := (C ((-2 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06637 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10062 ^ 1)
theorem ha10063 : a10063.IsHomogeneous 45 := by
  unfold a10063
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06637.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10062.pow 1)))

@[irreducible]
def a10064 : Poly := (C ((-32 : ℂ) / (7 : ℂ)) * a10061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10063 ^ 1)
theorem ha10064 : a10064.IsHomogeneous 45 := by
  unfold a10064
  exact ((((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (7 : ℂ))).mul (ha10061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10059.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10063.pow 1)))

@[irreducible]
def a10065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10060 ^ 1) + (C ((7 : ℂ) / (9720 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1)
theorem ha10065 : a10065.IsHomogeneous 45 := by
  unfold a10065
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10060.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (9720 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)))

@[irreducible]
def a10066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10061 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10065 ^ 1) + (C ((7 : ℂ) / (6480 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1)
theorem ha10066 : a10066.IsHomogeneous 45 := by
  unfold a10066
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10065.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6480 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)))

@[irreducible]
def a10067 : Poly := (C ((-4 : ℂ) / (1215 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10062 ^ 1)
theorem ha10067 : a10067.IsHomogeneous 45 := by
  unfold a10067
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10062.pow 1)))

@[irreducible]
def a10068 : Poly := (C ((-2 : ℂ) / (405 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a06672 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10063 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a10067 ^ 1)
theorem ha10068 : a10068.IsHomogeneous 45 := by
  unfold a10068
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha06672.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10063.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha10067.pow 1)))

@[irreducible]
def a10069 : Poly := (C ((-32 : ℂ) / (7 : ℂ)) * a10066 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10064 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10068 ^ 1)
theorem ha10069 : a10069.IsHomogeneous 45 := by
  unfold a10069
  exact ((((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (7 : ℂ))).mul (ha10066.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10064.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10068.pow 1)))

@[irreducible]
def a10070 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a10037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10021 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a10010 ^ 1) + (C ((14 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a10069 ^ 1)
theorem ha10070 : a10070.IsHomogeneous 50 := by
  unfold a10070
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha10037.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10021.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha10010.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha10069.pow 1)))

@[irreducible]
def a10071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00931 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a02104 ^ 1)
theorem ha10071 : a10071.IsHomogeneous 240 := by
  unfold a10071
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00931.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a10072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a04232 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a02104 ^ 1)
theorem ha10072 : a10072.IsHomogeneous 278 := by
  unfold a10072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha04232.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a10073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10072 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10071 ^ 1)
theorem ha10073 : a10073.IsHomogeneous 278 := by
  unfold a10073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10072.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10071.pow 1)))

@[irreducible]
def a10074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a01678 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00362 ^ 1 * a03534 ^ 1)
theorem ha10074 : a10074.IsHomogeneous 198 := by
  unfold a10074
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha01678.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a10075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a10074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10071 ^ 1)
theorem ha10075 : a10075.IsHomogeneous 240 := by
  unfold a10075
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha10074.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10071.pow 1)))

@[irreducible]
def a10076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10073 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10075 ^ 1)
theorem ha10076 : a10076.IsHomogeneous 278 := by
  unfold a10076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10073.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10075.pow 1)))

@[irreducible]
def a10077 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a04232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a07779 ^ 1)
theorem ha10077 : a10077.IsHomogeneous 314 := by
  unfold a10077
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha04232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha07779.pow 1)))

@[irreducible]
def a10078 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a10072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10077 ^ 1)
theorem ha10078 : a10078.IsHomogeneous 314 := by
  unfold a10078
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha10072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10077.pow 1)))

@[irreducible]
def a10079 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a10073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10078 ^ 1)
theorem ha10079 : a10079.IsHomogeneous 314 := by
  unfold a10079
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha10073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10078.pow 1)))

@[irreducible]
def a10080 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a10076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10079 ^ 1)
theorem ha10080 : a10080.IsHomogeneous 314 := by
  unfold a10080
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha10076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10079.pow 1)))

@[irreducible]
def a10081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00637 ^ 1 * a00880 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00327 ^ 1 * a01581 ^ 1)
theorem ha10081 : a10081.IsHomogeneous 196 := by
  unfold a10081
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00637.pow 1)).mul (ha00880.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a10082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00637 ^ 1 * a00880 ^ 1)
theorem ha10082 : a10082.IsHomogeneous 234 := by
  unfold a10082
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha02041.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00637.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a10083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10082 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10081 ^ 1)
theorem ha10083 : a10083.IsHomogeneous 234 := by
  unfold a10083
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10082.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10081.pow 1)))

@[irreducible]
def a10084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a01581 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a00134 ^ 1 * a03370 ^ 1)
theorem ha10084 : a10084.IsHomogeneous 160 := by
  unfold a10084
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha01581.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha03370.pow 1)))

@[irreducible]
def a10085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10081 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a10084 ^ 1)
theorem ha10085 : a10085.IsHomogeneous 196 := by
  unfold a10085
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10081.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha10084.pow 1)))

@[irreducible]
def a10086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10083 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a10085 ^ 1)
theorem ha10086 : a10086.IsHomogeneous 234 := by
  unfold a10086
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10083.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha10085.pow 1)))

@[irreducible]
def a10087 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a04148 ^ 1)
theorem ha10087 : a10087.IsHomogeneous 270 := by
  unfold a10087
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha04148.pow 1)))

@[irreducible]
def a10088 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a10082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10087 ^ 1)
theorem ha10088 : a10088.IsHomogeneous 270 := by
  unfold a10088
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha10082.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10087.pow 1)))

@[irreducible]
def a10089 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a10083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10088 ^ 1)
theorem ha10089 : a10089.IsHomogeneous 270 := by
  unfold a10089
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha10083.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10088.pow 1)))

@[irreducible]
def a10090 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00100 ^ 1 * a10086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10089 ^ 1)
theorem ha10090 : a10090.IsHomogeneous 270 := by
  unfold a10090
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00100.pow 1)).mul (ha10086.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10089.pow 1)))

@[irreducible]
def a10091 : Poly := (C ((-864 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a10090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a10080 ^ 1)
theorem ha10091 : a10091.IsHomogeneous 319 := by
  unfold a10091
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-864 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha10090.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha10080.pow 1)))

@[irreducible]
def a10092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10091 ^ 1) + (C ((1 : ℂ) / (10800 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 6 * a00100 ^ 6 * a10070 ^ 1)
theorem ha10092 : a10092.IsHomogeneous 319 := by
  unfold a10092
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10091.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10800 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00100.pow 6)).mul (ha10070.pow 1)))

@[irreducible]
def a10093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a05293 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a10092 ^ 1)
theorem ha10093 : a10093.IsHomogeneous 319 := by
  unfold a10093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha05293.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha10092.pow 1)))

@[irreducible]
def a10094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10093 ^ 1)
theorem ha10094 : a10094.IsHomogeneous 319 := by
  unfold a10094
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10093.pow 1)))

@[irreducible]
def a10095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10094 ^ 1)
theorem ha10095 : a10095.IsHomogeneous 319 := by
  unfold a10095
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10094.pow 1)))

@[irreducible]
def a10096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10095 ^ 1)
theorem ha10096 : a10096.IsHomogeneous 319 := by
  unfold a10096
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09939.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10095.pow 1)))

@[irreducible]
def a10097 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a10096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a05296 ^ 1)
theorem ha10097 : a10097.IsHomogeneous 877 := by
  unfold a10097
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha10096.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha05296.pow 1)))

@[irreducible]
def a10098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09932 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a10097 ^ 1)
theorem ha10098 : a10098.IsHomogeneous 1324 := by
  unfold a10098
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09932.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha10097.pow 1)))

@[irreducible]
def a10099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a09933 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a10098 ^ 1)
theorem ha10099 : a10099.IsHomogeneous 1741 := by
  unfold a10099
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha09933.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha10098.pow 1)))

@[irreducible]
def a10100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a04155 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a01180 ^ 1 * a02046 ^ 1)
theorem ha10100 : a10100.IsHomogeneous 2158 := by
  unfold a10100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha04155.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha01180.pow 1)).mul (ha02046.pow 1)))

@[irreducible]
def a10101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10100 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09931 ^ 1)
theorem ha10101 : a10101.IsHomogeneous 2158 := by
  unfold a10101
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10100.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09931.pow 1)))

@[irreducible]
def a10102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10101 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a09933 ^ 1)
theorem ha10102 : a10102.IsHomogeneous 2158 := by
  unfold a10102
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10101.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha09933.pow 1)))

@[irreducible]
def a10103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10102 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a10099 ^ 1)
theorem ha10103 : a10103.IsHomogeneous 2158 := by
  unfold a10103
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10102.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha10099.pow 1)))

@[irreducible]
def a10104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a10103 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00134 ^ 5 * a09930 ^ 1)
theorem ha10104 : a10104.IsHomogeneous 2236 := by
  unfold a10104
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha10103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 5)).mul (ha09930.pow 1)))

@[irreducible]
def a10105 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02043 ^ 1 * a02109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a04239 ^ 1)
theorem ha10105 : a10105.IsHomogeneous 2300 := by
  unfold a10105
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02043.pow 1)).mul (ha02109.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha04239.pow 1)))

@[irreducible]
def a10106 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a04239 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a07788 ^ 1)
theorem ha10106 : a10106.IsHomogeneous 2657 := by
  unfold a10106
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha04239.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha07788.pow 1)))

@[irreducible]
def a10107 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10106 ^ 1)
theorem ha10107 : a10107.IsHomogeneous 2657 := by
  unfold a10107
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10105.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10106.pow 1)))

@[irreducible]
def a10108 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00934 ^ 1 * a04151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02043 ^ 1 * a02109 ^ 1)
theorem ha10108 : a10108.IsHomogeneous 1943 := by
  unfold a10108
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00934.pow 1)).mul (ha04151.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02043.pow 1)).mul (ha02109.pow 1)))

@[irreducible]
def a10109 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10108 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10105 ^ 1)
theorem ha10109 : a10109.IsHomogeneous 2300 := by
  unfold a10109
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10108.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10105.pow 1)))

@[irreducible]
def a10110 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10107 ^ 1)
theorem ha10110 : a10110.IsHomogeneous 2657 := by
  unfold a10110
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10107.pow 1)))

@[irreducible]
def a10111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01196 ^ 1 * a01949 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a02687 ^ 1)
theorem ha10111 : a10111.IsHomogeneous 1433 := by
  unfold a10111
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01196.pow 1)).mul (ha01949.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a10112 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01196 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a03978 ^ 1)
theorem ha10112 : a10112.IsHomogeneous 1160 := by
  unfold a10112
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01196.pow 1)).mul (ha01949.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a10113 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10112 ^ 1)
theorem ha10113 : a10113.IsHomogeneous 1493 := by
  unfold a10113
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10111.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10112.pow 1)))

@[irreducible]
def a10114 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a05350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a02687 ^ 1)
theorem ha10114 : a10114.IsHomogeneous 1706 := by
  unfold a10114
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha05350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a10115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10111 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10114 ^ 1)
theorem ha10115 : a10115.IsHomogeneous 1766 := by
  unfold a10115
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10111.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10114.pow 1)))

@[irreducible]
def a10116 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10113 ^ 1)
theorem ha10116 : a10116.IsHomogeneous 1826 := by
  unfold a10116
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10115.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10113.pow 1)))

@[irreducible]
def a10117 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a02684 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01194 ^ 1 * a01707 ^ 1)
theorem ha10117 : a10117.IsHomogeneous 1175 := by
  unfold a10117
  exact (((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha02684.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01194.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a10118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00451 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a01194 ^ 1 * a01707 ^ 1)
theorem ha10118 : a10118.IsHomogeneous 1000 := by
  unfold a10118
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00451.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha01194.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a10119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10118 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a10117 ^ 1)
theorem ha10119 : a10119.IsHomogeneous 1254 := by
  unfold a10119
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha10117.pow 1)))

@[irreducible]
def a10120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a02684 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a05346 ^ 1)
theorem ha10120 : a10120.IsHomogeneous 1350 := by
  unfold a10120
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha02684.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha05346.pow 1)))

@[irreducible]
def a10121 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10117 ^ 1)
theorem ha10121 : a10121.IsHomogeneous 1429 := by
  unfold a10121
  exact ((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10120.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10117.pow 1)))

@[irreducible]
def a10122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10119 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a10121 ^ 1)
theorem ha10122 : a10122.IsHomogeneous 1508 := by
  unfold a10122
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10119.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha10121.pow 1)))

@[irreducible]
def a10123 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00451 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a06734 ^ 1)
theorem ha10123 : a10123.IsHomogeneous 825 := by
  unfold a10123
  exact (((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00451.pow 1)).mul (ha03569.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha06734.pow 1)))

@[irreducible]
def a10124 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10123 ^ 1)
theorem ha10124 : a10124.IsHomogeneous 1079 := by
  unfold a10124
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10118.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10123.pow 1)))

@[irreducible]
def a10125 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10124 ^ 1)
theorem ha10125 : a10125.IsHomogeneous 1333 := by
  unfold a10125
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10119.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10124.pow 1)))

@[irreducible]
def a10126 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10125 ^ 1)
theorem ha10126 : a10126.IsHomogeneous 1587 := by
  unfold a10126
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10122.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10125.pow 1)))

@[irreducible]
def a10127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a02681 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a01192 ^ 1 * a01871 ^ 1)
theorem ha10127 : a10127.IsHomogeneous 938 := by
  unfold a10127
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha02681.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha01192.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a10128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00450 ^ 1 * a03851 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01192 ^ 1 * a01871 ^ 1)
theorem ha10128 : a10128.IsHomogeneous 1192 := by
  unfold a10128
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00450.pow 1)).mul (ha03851.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01192.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a10129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10128 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10127 ^ 1)
theorem ha10129 : a10129.IsHomogeneous 1192 := by
  unfold a10129
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10128.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10127.pow 1)))

@[irreducible]
def a10130 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a05342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a02681 ^ 1)
theorem ha10130 : a10130.IsHomogeneous 683 := by
  unfold a10130
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha05342.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha02681.pow 1)))

@[irreducible]
def a10131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10127 ^ 1)
theorem ha10131 : a10131.IsHomogeneous 938 := by
  unfold a10131
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10127.pow 1)))

@[irreducible]
def a10132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10129 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10131 ^ 1)
theorem ha10132 : a10132.IsHomogeneous 1192 := by
  unfold a10132
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10129.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10131.pow 1)))

@[irreducible]
def a10133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00136 ^ 1 * a07192 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00450 ^ 1 * a03851 ^ 1)
theorem ha10133 : a10133.IsHomogeneous 1446 := by
  unfold a10133
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00136.pow 1)).mul (ha07192.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00450.pow 1)).mul (ha03851.pow 1)))

@[irreducible]
def a10134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10133 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10128 ^ 1)
theorem ha10134 : a10134.IsHomogeneous 1446 := by
  unfold a10134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10133.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10128.pow 1)))

@[irreducible]
def a10135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10134 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10129 ^ 1)
theorem ha10135 : a10135.IsHomogeneous 1446 := by
  unfold a10135
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10134.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10129.pow 1)))

@[irreducible]
def a10136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10135 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10132 ^ 1)
theorem ha10136 : a10136.IsHomogeneous 1446 := by
  unfold a10136
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10135.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10132.pow 1)))

@[irreducible]
def a10137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01186 ^ 1 * a01877 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00798 ^ 1 * a02671 ^ 1)
theorem ha10137 : a10137.IsHomogeneous 139 := by
  unfold a10137
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01186.pow 1)).mul (ha01877.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00798.pow 1)).mul (ha02671.pow 1)))

@[irreducible]
def a10138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01186 ^ 1 * a01877 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00447 ^ 1 * a03861 ^ 1)
theorem ha10138 : a10138.IsHomogeneous 139 := by
  unfold a10138
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01186.pow 1)).mul (ha01877.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00447.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a10139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10138 ^ 1)
theorem ha10139 : a10139.IsHomogeneous 139 := by
  unfold a10139
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10138.pow 1)))

@[irreducible]
def a10140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00293 ^ 1 * a05327 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a00798 ^ 1 * a02671 ^ 1)
theorem ha10140 : a10140.IsHomogeneous 139 := by
  unfold a10140
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00293.pow 1)).mul (ha05327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha00798.pow 1)).mul (ha02671.pow 1)))

@[irreducible]
def a10141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10137 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a10140 ^ 1)
theorem ha10141 : a10141.IsHomogeneous 139 := by
  unfold a10141
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha10140.pow 1)))

@[irreducible]
def a10142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10141 ^ 1)
theorem ha10142 : a10142.IsHomogeneous 139 := by
  unfold a10142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10141.pow 1)))

@[irreducible]
def a10143 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00447 ^ 1 * a03861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00135 ^ 1 * a07207 ^ 1)
theorem ha10143 : a10143.IsHomogeneous 133 := by
  unfold a10143
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00447.pow 1)).mul (ha03861.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00135.pow 1)).mul (ha07207.pow 1)))

@[irreducible]
def a10144 : Poly := (C ((-15 : ℂ) / (4 : ℂ)) * a10138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10143 ^ 1)
theorem ha10144 : a10144.IsHomogeneous 139 := by
  unfold a10144
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (4 : ℂ))).mul (ha10138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10143.pow 1)))

@[irreducible]
def a10145 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a10144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10139 ^ 1)
theorem ha10145 : a10145.IsHomogeneous 139 := by
  unfold a10145
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha10144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10139.pow 1)))

@[irreducible]
def a10146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10145 ^ 1)
theorem ha10146 : a10146.IsHomogeneous 139 := by
  unfold a10146
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10145.pow 1)))

@[irreducible]
def a10147 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a06725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a06692 ^ 1)
theorem ha10147 : a10147.IsHomogeneous 56 := by
  unfold a10147
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha06692.pow 1)))

@[irreducible]
def a10148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00125 ^ 1 * a10147 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a05327 ^ 1)
theorem ha10148 : a10148.IsHomogeneous 133 := by
  unfold a10148
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha10147.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha05327.pow 1)))

@[irreducible]
def a10149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10148 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a10140 ^ 1)
theorem ha10149 : a10149.IsHomogeneous 139 := by
  unfold a10149
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha10140.pow 1)))

@[irreducible]
def a10150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10141 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a10149 ^ 1)
theorem ha10150 : a10150.IsHomogeneous 139 := by
  unfold a10150
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha10149.pow 1)))

@[irreducible]
def a10151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10150 ^ 1)
theorem ha10151 : a10151.IsHomogeneous 139 := by
  unfold a10151
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10150.pow 1)))

@[irreducible]
def a10152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10151 ^ 1)
theorem ha10152 : a10152.IsHomogeneous 139 := by
  unfold a10152
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10151.pow 1)))

@[irreducible]
def a10153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00713 ^ 1 * a01702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00712 ^ 1 * a01703 ^ 1)
theorem ha10153 : a10153.IsHomogeneous 141 := by
  unfold a10153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00713.pow 1)).mul (ha01702.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a10154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00713 ^ 1 * a01702 ^ 1) + (C ((32 : ℂ) / (135 : ℂ)) * a00014 ^ 1 * a00261 ^ 1 * a03562 ^ 1)
theorem ha10154 : a10154.IsHomogeneous 142 := by
  unfold a10154
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00713.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (135 : ℂ))).mul (ha00014.pow 1)).mul (ha00261.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10154 ^ 1)
theorem ha10155 : a10155.IsHomogeneous 142 := by
  unfold a10155
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10154.pow 1)))

@[irreducible]
def a10156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a01703 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a03563 ^ 1)
theorem ha10156 : a10156.IsHomogeneous 136 := by
  unfold a10156
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha01703.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha03563.pow 1)))

@[irreducible]
def a10157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a10153 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a10156 ^ 1)
theorem ha10157 : a10157.IsHomogeneous 142 := by
  unfold a10157
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha10153.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha10156.pow 1)))

@[irreducible]
def a10158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10157 ^ 1)
theorem ha10158 : a10158.IsHomogeneous 142 := by
  unfold a10158
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10157.pow 1)))

@[irreducible]
def a10159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00101 ^ 1 * a06725 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a00261 ^ 1 * a03562 ^ 1)
theorem ha10159 : a10159.IsHomogeneous 136 := by
  unfold a10159
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha00261.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a10160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10159 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a10154 ^ 1)
theorem ha10160 : a10160.IsHomogeneous 142 := by
  unfold a10160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha10154.pow 1)))

@[irreducible]
def a10161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10155 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a10160 ^ 1)
theorem ha10161 : a10161.IsHomogeneous 142 := by
  unfold a10161
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha10160.pow 1)))

@[irreducible]
def a10162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10161 ^ 1)
theorem ha10162 : a10162.IsHomogeneous 142 := by
  unfold a10162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10161.pow 1)))

@[irreducible]
def a10163 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03563 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a06726 ^ 1)
theorem ha10163 : a10163.IsHomogeneous 130 := by
  unfold a10163
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03563.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06726.pow 1)))

@[irreducible]
def a10164 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a10163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10156 ^ 1)
theorem ha10164 : a10164.IsHomogeneous 136 := by
  unfold a10164
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha10163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10156.pow 1)))

@[irreducible]
def a10165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a10164 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a10157 ^ 1)
theorem ha10165 : a10165.IsHomogeneous 142 := by
  unfold a10165
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha10164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha10157.pow 1)))

@[irreducible]
def a10166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10158 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a10165 ^ 1)
theorem ha10166 : a10166.IsHomogeneous 142 := by
  unfold a10166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha10165.pow 1)))

@[irreducible]
def a10167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10166 ^ 1)
theorem ha10167 : a10167.IsHomogeneous 142 := by
  unfold a10167
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10166.pow 1)))

@[irreducible]
def a10168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a10152 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00001 ^ 1 * a10167 ^ 1)
theorem ha10168 : a10168.IsHomogeneous 143 := by
  unfold a10168
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha10152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00001.pow 1)).mul (ha10167.pow 1)))

@[irreducible]
def a10169 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a05342 ^ 1)
theorem ha10169 : a10169.IsHomogeneous 428 := by
  unfold a10169
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha05342.pow 1)))

@[irreducible]
def a10170 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10130 ^ 1)
theorem ha10170 : a10170.IsHomogeneous 683 := by
  unfold a10170
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10130.pow 1)))

@[irreducible]
def a10171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10131 ^ 1)
theorem ha10171 : a10171.IsHomogeneous 938 := by
  unfold a10171
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10131.pow 1)))

@[irreducible]
def a10172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10132 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10171 ^ 1)
theorem ha10172 : a10172.IsHomogeneous 1192 := by
  unfold a10172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10132.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10171.pow 1)))

@[irreducible]
def a10173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10136 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10172 ^ 1)
theorem ha10173 : a10173.IsHomogeneous 1446 := by
  unfold a10173
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10136.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10172.pow 1)))

@[irreducible]
def a10174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a05346 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a10173 ^ 1)
theorem ha10174 : a10174.IsHomogeneous 1525 := by
  unfold a10174
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha05346.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha10173.pow 1)))

@[irreducible]
def a10175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10120 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a10174 ^ 1)
theorem ha10175 : a10175.IsHomogeneous 1604 := by
  unfold a10175
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10120.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha10174.pow 1)))

@[irreducible]
def a10176 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10175 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10121 ^ 1)
theorem ha10176 : a10176.IsHomogeneous 1683 := by
  unfold a10176
  exact ((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10175.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10121.pow 1)))

@[irreducible]
def a10177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10122 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a10176 ^ 1)
theorem ha10177 : a10177.IsHomogeneous 1762 := by
  unfold a10177
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha10176.pow 1)))

@[irreducible]
def a10178 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a10177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10126 ^ 1)
theorem ha10178 : a10178.IsHomogeneous 1841 := by
  unfold a10178
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha10177.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10126.pow 1)))

@[irreducible]
def a10179 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a10178 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a05350 ^ 1)
theorem ha10179 : a10179.IsHomogeneous 1949 := by
  unfold a10179
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha10178.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha05350.pow 1)))

@[irreducible]
def a10180 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a10179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10114 ^ 1)
theorem ha10180 : a10180.IsHomogeneous 2039 := by
  unfold a10180
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha10179.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10114.pow 1)))

@[irreducible]
def a10181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10115 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10180 ^ 1)
theorem ha10181 : a10181.IsHomogeneous 2099 := by
  unfold a10181
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10115.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10180.pow 1)))

@[irreducible]
def a10182 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10116 ^ 1)
theorem ha10182 : a10182.IsHomogeneous 2159 := by
  unfold a10182
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10181.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10116.pow 1)))

@[irreducible]
def a10183 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a03978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a07382 ^ 1)
theorem ha10183 : a10183.IsHomogeneous 887 := by
  unfold a10183
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha03978.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha07382.pow 1)))

@[irreducible]
def a10184 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10183 ^ 1)
theorem ha10184 : a10184.IsHomogeneous 1220 := by
  unfold a10184
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10112.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10183.pow 1)))

@[irreducible]
def a10185 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10184 ^ 1)
theorem ha10185 : a10185.IsHomogeneous 1553 := by
  unfold a10185
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10113.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10184.pow 1)))

@[irreducible]
def a10186 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10185 ^ 1)
theorem ha10186 : a10186.IsHomogeneous 1886 := by
  unfold a10186
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10116.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10185.pow 1)))

@[irreducible]
def a10187 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10186 ^ 1)
theorem ha10187 : a10187.IsHomogeneous 2219 := by
  unfold a10187
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10182.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10186.pow 1)))

@[irreducible]
def a10188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01196 ^ 1 * a01979 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a02687 ^ 1)
theorem ha10188 : a10188.IsHomogeneous 1361 := by
  unfold a10188
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01196.pow 1)).mul (ha01979.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a10189 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a01196 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a04032 ^ 1)
theorem ha10189 : a10189.IsHomogeneous 1064 := by
  unfold a10189
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha01196.pow 1)).mul (ha01979.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a10190 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a10188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10189 ^ 1)
theorem ha10190 : a10190.IsHomogeneous 1397 := by
  unfold a10190
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha10188.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10189.pow 1)))

@[irreducible]
def a10191 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a05350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a02687 ^ 1)
theorem ha10191 : a10191.IsHomogeneous 1658 := by
  unfold a10191
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha05350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a10192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10188 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a10191 ^ 1)
theorem ha10192 : a10192.IsHomogeneous 1694 := by
  unfold a10192
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha10191.pow 1)))

@[irreducible]
def a10193 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a10192 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10190 ^ 1)
theorem ha10193 : a10193.IsHomogeneous 1730 := by
  unfold a10193
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha10192.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10190.pow 1)))

@[irreducible]
def a10194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a05350 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a10178 ^ 1)
theorem ha10194 : a10194.IsHomogeneous 1925 := by
  unfold a10194
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha05350.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha10178.pow 1)))

@[irreducible]
def a10195 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a10194 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10191 ^ 1)
theorem ha10195 : a10195.IsHomogeneous 1991 := by
  unfold a10195
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha10194.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10191.pow 1)))

@[irreducible]
def a10196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10192 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a10195 ^ 1)
theorem ha10196 : a10196.IsHomogeneous 2027 := by
  unfold a10196
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10192.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha10195.pow 1)))

@[irreducible]
def a10197 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a10196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10193 ^ 1)
theorem ha10197 : a10197.IsHomogeneous 2063 := by
  unfold a10197
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha10196.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10193.pow 1)))

@[irreducible]
def a10198 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a04032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a07468 ^ 1)
theorem ha10198 : a10198.IsHomogeneous 767 := by
  unfold a10198
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha04032.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha07468.pow 1)))

@[irreducible]
def a10199 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10189 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10198 ^ 1)
theorem ha10199 : a10199.IsHomogeneous 1100 := by
  unfold a10199
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10189.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10198.pow 1)))

@[irreducible]
def a10200 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10199 ^ 1)
theorem ha10200 : a10200.IsHomogeneous 1433 := by
  unfold a10200
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10190.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10199.pow 1)))

@[irreducible]
def a10201 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10193 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10200 ^ 1)
theorem ha10201 : a10201.IsHomogeneous 1766 := by
  unfold a10201
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10193.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10200.pow 1)))

@[irreducible]
def a10202 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a10197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10201 ^ 1)
theorem ha10202 : a10202.IsHomogeneous 2099 := by
  unfold a10202
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha10197.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10201.pow 1)))

@[irreducible]
def a10203 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a01290 ^ 1 * a01886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a02860 ^ 1)
theorem ha10203 : a10203.IsHomogeneous 1501 := by
  unfold a10203
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01290.pow 1)).mul (ha01886.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha02860.pow 1)))

@[irreducible]
def a10204 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01290 ^ 1 * a01886 ^ 1)
theorem ha10204 : a10204.IsHomogeneous 1774 := by
  unfold a10204
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01290.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a10205 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10204 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10203 ^ 1)
theorem ha10205 : a10205.IsHomogeneous 1834 := by
  unfold a10205
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10204.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10203.pow 1)))

@[irreducible]
def a10206 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a02860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a05627 ^ 1)
theorem ha10206 : a10206.IsHomogeneous 1228 := by
  unfold a10206
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha02860.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha05627.pow 1)))

@[irreducible]
def a10207 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10206 ^ 1)
theorem ha10207 : a10207.IsHomogeneous 1561 := by
  unfold a10207
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10203.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10206.pow 1)))

@[irreducible]
def a10208 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10205 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10207 ^ 1)
theorem ha10208 : a10208.IsHomogeneous 1894 := by
  unfold a10208
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10205.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10207.pow 1)))

@[irreducible]
def a10209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a03873 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a07222 ^ 1)
theorem ha10209 : a10209.IsHomogeneous 2047 := by
  unfold a10209
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha03873.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a10210 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10204 ^ 1)
theorem ha10210 : a10210.IsHomogeneous 2107 := by
  unfold a10210
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10209.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10204.pow 1)))

@[irreducible]
def a10211 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10205 ^ 1)
theorem ha10211 : a10211.IsHomogeneous 2167 := by
  unfold a10211
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10210.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10205.pow 1)))

@[irreducible]
def a10212 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a10211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a10208 ^ 1)
theorem ha10212 : a10212.IsHomogeneous 2227 := by
  unfold a10212
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha10211.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha10208.pow 1)))

@[irreducible]
def a10213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a02857 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a01288 ^ 1 * a01946 ^ 1)
theorem ha10213 : a10213.IsHomogeneous 493 := by
  unfold a10213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha02857.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha01288.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a10214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00491 ^ 1 * a03974 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a01288 ^ 1 * a01946 ^ 1)
theorem ha10214 : a10214.IsHomogeneous 493 := by
  unfold a10214
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00491.pow 1)).mul (ha03974.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha01288.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a10215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10213 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a10214 ^ 1)
theorem ha10215 : a10215.IsHomogeneous 493 := by
  unfold a10215
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha10214.pow 1)))

@[irreducible]
def a10216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a05623 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00834 ^ 1 * a02857 ^ 1)
theorem ha10216 : a10216.IsHomogeneous 493 := by
  unfold a10216
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha05623.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00834.pow 1)).mul (ha02857.pow 1)))

@[irreducible]
def a10217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10213 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a10216 ^ 1)
theorem ha10217 : a10217.IsHomogeneous 493 := by
  unfold a10217
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha10216.pow 1)))

@[irreducible]
def a10218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10217 ^ 1)
theorem ha10218 : a10218.IsHomogeneous 493 := by
  unfold a10218
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10217.pow 1)))

@[irreducible]
def a10219 : Poly := (C ((-1 : ℂ) / (15 : ℂ)) * a00491 ^ 1 * a03974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00151 ^ 1 * a07377 ^ 1)
theorem ha10219 : a10219.IsHomogeneous 493 := by
  unfold a10219
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15 : ℂ))).mul (ha00491.pow 1)).mul (ha03974.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha07377.pow 1)))

@[irreducible]
def a10220 : Poly := (C ((-15 : ℂ) / (1 : ℂ)) * a10219 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10214 ^ 1)
theorem ha10220 : a10220.IsHomogeneous 493 := by
  unfold a10220
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (1 : ℂ))).mul (ha10219.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10214.pow 1)))

@[irreducible]
def a10221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10215 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a10220 ^ 1)
theorem ha10221 : a10221.IsHomogeneous 493 := by
  unfold a10221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha10220.pow 1)))

@[irreducible]
def a10222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10218 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10221 ^ 1)
theorem ha10222 : a10222.IsHomogeneous 493 := by
  unfold a10222
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10218.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10221.pow 1)))

@[irreducible]
def a10223 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01207 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a02710 ^ 1)
theorem ha10223 : a10223.IsHomogeneous 138 := by
  unfold a10223
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01207.pow 1)).mul (ha01923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a03933 ^ 1)
theorem ha10224 : a10224.IsHomogeneous 141 := by
  unfold a10224
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).mul (ha01923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha03933.pow 1)))

@[irreducible]
def a10225 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10224 ^ 1)
theorem ha10225 : a10225.IsHomogeneous 141 := by
  unfold a10225
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10224.pow 1)))

@[irreducible]
def a10226 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00303 ^ 1 * a05389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a02710 ^ 1)
theorem ha10226 : a10226.IsHomogeneous 138 := by
  unfold a10226
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha05389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a10227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10226 ^ 1)
theorem ha10227 : a10227.IsHomogeneous 138 := by
  unfold a10227
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10226.pow 1)))

@[irreducible]
def a10228 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a10227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10225 ^ 1)
theorem ha10228 : a10228.IsHomogeneous 141 := by
  unfold a10228
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha10227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10225.pow 1)))

@[irreducible]
def a10229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00864 ^ 1)
theorem ha10229 : a10229.IsHomogeneous 18 := by
  unfold a10229
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00864.pow 1)))

@[irreducible]
def a10230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10229 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a02979 ^ 1)
theorem ha10230 : a10230.IsHomogeneous 18 := by
  unfold a10230
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10229.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha02979.pow 1)))

@[irreducible]
def a10231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10230 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a02980 ^ 1)
theorem ha10231 : a10231.IsHomogeneous 18 := by
  unfold a10231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10230.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha02980.pow 1)))

@[irreducible]
def a10232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02981 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a10231 ^ 1)
theorem ha10232 : a10232.IsHomogeneous 18 := by
  unfold a10232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02981.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha10231.pow 1)))

@[irreducible]
def a10233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a04085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02007 ^ 1)
theorem ha10233 : a10233.IsHomogeneous 18 := by
  unfold a10233
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a10234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10229 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a10233 ^ 1)
theorem ha10234 : a10234.IsHomogeneous 18 := by
  unfold a10234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10229.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha10233.pow 1)))

@[irreducible]
def a10235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10234 ^ 1)
theorem ha10235 : a10235.IsHomogeneous 18 := by
  unfold a10235
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10234.pow 1)))

@[irreducible]
def a10236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10235 ^ 1)
theorem ha10236 : a10236.IsHomogeneous 18 := by
  unfold a10236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10235.pow 1)))

@[irreducible]
def a10237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10232 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a10236 ^ 1)
theorem ha10237 : a10237.IsHomogeneous 18 := by
  unfold a10237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha10236.pow 1)))

@[irreducible]
def a10238 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a10237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a05389 ^ 1)
theorem ha10238 : a10238.IsHomogeneous 132 := by
  unfold a10238
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha10237.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha05389.pow 1)))

@[irreducible]
def a10239 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a10238 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10226 ^ 1)
theorem ha10239 : a10239.IsHomogeneous 138 := by
  unfold a10239
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha10238.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10226.pow 1)))

end CycleQ2Concrete
