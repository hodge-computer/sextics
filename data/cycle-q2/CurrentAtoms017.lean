import Proposal.CurrentAtoms016

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a06144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06137 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06143 ^ 1)
theorem ha06144 : a06144.IsHomogeneous 18 := by
  unfold a06144
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06143.pow 1)))

@[irreducible]
def a06145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06144 ^ 1)
theorem ha06145 : a06145.IsHomogeneous 18 := by
  unfold a06145
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06144.pow 1)))

@[irreducible]
def a06146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06145 ^ 1)
theorem ha06146 : a06146.IsHomogeneous 18 := by
  unfold a06146
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06145.pow 1)))

@[irreducible]
def a06147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6)
theorem ha06147 : a06147.IsHomogeneous 6 := by
  unfold a06147
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a06148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06147 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha06148 : a06148.IsHomogeneous 6 := by
  unfold a06148
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a06149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1)
theorem ha06149 : a06149.IsHomogeneous 6 := by
  unfold a06149
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)))

@[irreducible]
def a06150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06147 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06149 ^ 1)
theorem ha06150 : a06150.IsHomogeneous 6 := by
  unfold a06150
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06149.pow 1)))

@[irreducible]
def a06151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06150 ^ 1)
theorem ha06151 : a06151.IsHomogeneous 6 := by
  unfold a06151
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06150.pow 1)))

@[irreducible]
def a06152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06148 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06151 ^ 1)
theorem ha06152 : a06152.IsHomogeneous 6 := by
  unfold a06152
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06151.pow 1)))

@[irreducible]
def a06153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a03186 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06152 ^ 1)
theorem ha06153 : a06153.IsHomogeneous 12 := by
  unfold a06153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06152.pow 1)))

@[irreducible]
def a06154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06143 ^ 1)
theorem ha06154 : a06154.IsHomogeneous 18 := by
  unfold a06154
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06143.pow 1)))

@[irreducible]
def a06155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06144 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06154 ^ 1)
theorem ha06155 : a06155.IsHomogeneous 18 := by
  unfold a06155
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06154.pow 1)))

@[irreducible]
def a06156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06155 ^ 1)
theorem ha06156 : a06156.IsHomogeneous 18 := by
  unfold a06156
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06155.pow 1)))

@[irreducible]
def a06157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06156 ^ 1)
theorem ha06157 : a06157.IsHomogeneous 18 := by
  unfold a06157
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06156.pow 1)))

@[irreducible]
def a06158 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a06136 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06109 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a06157 ^ 1)
theorem ha06158 : a06158.IsHomogeneous 18 := by
  unfold a06158
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha06136.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06109.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha06157.pow 1)))

@[irreducible]
def a06159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a03191 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06158 ^ 1)
theorem ha06159 : a06159.IsHomogeneous 24 := by
  unfold a06159
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06158.pow 1)))

@[irreducible]
def a06160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06069 ^ 1)
theorem ha06160 : a06160.IsHomogeneous 36 := by
  unfold a06160
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06069.pow 1)))

@[irreducible]
def a06161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06070 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06160 ^ 1)
theorem ha06161 : a06161.IsHomogeneous 36 := by
  unfold a06161
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06160.pow 1)))

@[irreducible]
def a06162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06071 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a06161 ^ 1)
theorem ha06162 : a06162.IsHomogeneous 36 := by
  unfold a06162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha06161.pow 1)))

@[irreducible]
def a06163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06075 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06162 ^ 1)
theorem ha06163 : a06163.IsHomogeneous 36 := by
  unfold a06163
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06075.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06162.pow 1)))

@[irreducible]
def a06164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a06065 ^ 1) + (C ((1 : ℂ) / (972 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a06163 ^ 1)
theorem ha06164 : a06164.IsHomogeneous 51 := by
  unfold a06164
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha06065.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha06163.pow 1)))

@[irreducible]
def a06165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a01340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00513 ^ 1 * a00865 ^ 1)
theorem ha06165 : a06165.IsHomogeneous 45 := by
  unfold a06165
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha01340.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00513.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01340 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a02956 ^ 1)
theorem ha06166 : a06166.IsHomogeneous 45 := by
  unfold a06166
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha02956.pow 1)))

@[irreducible]
def a06167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06165 ^ 1)
theorem ha06167 : a06167.IsHomogeneous 51 := by
  unfold a06167
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06166.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06165.pow 1)))

@[irreducible]
def a06168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00157 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a00865 ^ 1)
theorem ha06168 : a06168.IsHomogeneous 39 := by
  unfold a06168
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06165 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a06168 ^ 1)
theorem ha06169 : a06169.IsHomogeneous 45 := by
  unfold a06169
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06165.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha06168.pow 1)))

@[irreducible]
def a06170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06167 ^ 1)
theorem ha06170 : a06170.IsHomogeneous 51 := by
  unfold a06170
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06167.pow 1)))

@[irreducible]
def a06171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05784 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02956 ^ 1)
theorem ha06171 : a06171.IsHomogeneous 48 := by
  unfold a06171
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05784.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02956.pow 1)))

@[irreducible]
def a06172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06171 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06166 ^ 1)
theorem ha06172 : a06172.IsHomogeneous 48 := by
  unfold a06172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06166.pow 1)))

@[irreducible]
def a06173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06172 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a06167 ^ 1)
theorem ha06173 : a06173.IsHomogeneous 51 := by
  unfold a06173
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha06167.pow 1)))

@[irreducible]
def a06174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06170 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a06173 ^ 1)
theorem ha06174 : a06174.IsHomogeneous 51 := by
  unfold a06174
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha06173.pow 1)))

@[irreducible]
def a06175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a04086 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a02008 ^ 1)
theorem ha06175 : a06175.IsHomogeneous 30 := by
  unfold a06175
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06175 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a06168 ^ 1)
theorem ha06176 : a06176.IsHomogeneous 39 := by
  unfold a06176
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha06168.pow 1)))

@[irreducible]
def a06177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06169 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a06176 ^ 1)
theorem ha06177 : a06177.IsHomogeneous 45 := by
  unfold a06177
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06169.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha06176.pow 1)))

@[irreducible]
def a06178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06170 ^ 1)
theorem ha06178 : a06178.IsHomogeneous 51 := by
  unfold a06178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06177.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06170.pow 1)))

@[irreducible]
def a06179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06178 ^ 1)
theorem ha06179 : a06179.IsHomogeneous 51 := by
  unfold a06179
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06174.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06178.pow 1)))

@[irreducible]
def a06180 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a06065 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a06179 ^ 1)
theorem ha06180 : a06180.IsHomogeneous 57 := by
  unfold a06180
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha06065.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha06179.pow 1)))

@[irreducible]
def a06181 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a06164 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06180 ^ 1)
theorem ha06181 : a06181.IsHomogeneous 57 := by
  unfold a06181
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha06164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06180.pow 1)))

@[irreducible]
def a06182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a00506 ^ 1)
theorem ha06182 : a06182.IsHomogeneous 36 := by
  unfold a06182
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00168 ^ 1)
theorem ha06183 : a06183.IsHomogeneous 24 := by
  unfold a06183
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a06184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00547 ^ 1)
theorem ha06184 : a06184.IsHomogeneous 36 := by
  unfold a06184
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06183 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06182 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a06184 ^ 1)
theorem ha06185 : a06185.IsHomogeneous 36 := by
  unfold a06185
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06182.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha06184.pow 1)))

@[irreducible]
def a06186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00506 ^ 1)
theorem ha06186 : a06186.IsHomogeneous 24 := by
  unfold a06186
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a01327 ^ 1)
theorem ha06187 : a06187.IsHomogeneous 24 := by
  unfold a06187
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06186 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06187 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06182 ^ 1)
theorem ha06188 : a06188.IsHomogeneous 36 := by
  unfold a06188
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06187.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06182.pow 1)))

@[irreducible]
def a06189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00155 ^ 1 * a00168 ^ 1)
theorem ha06189 : a06189.IsHomogeneous 18 := by
  unfold a06189
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a06190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06183 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06186 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06189 ^ 1)
theorem ha06190 : a06190.IsHomogeneous 24 := by
  unfold a06190
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06186.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06189.pow 1)))

@[irreducible]
def a06191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06185 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06188 ^ 1)
theorem ha06191 : a06191.IsHomogeneous 36 := by
  unfold a06191
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06185.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06188.pow 1)))

@[irreducible]
def a06192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00547 ^ 1)
theorem ha06192 : a06192.IsHomogeneous 24 := by
  unfold a06192
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00547 ^ 1)
theorem ha06193 : a06193.IsHomogeneous 18 := by
  unfold a06193
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1)))

@[irreducible]
def a06194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06192 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a06193 ^ 1)
theorem ha06194 : a06194.IsHomogeneous 24 := by
  unfold a06194
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06192.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha06193.pow 1)))

@[irreducible]
def a06195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a01412 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1)
theorem ha06195 : a06195.IsHomogeneous 24 := by
  unfold a06195
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a06196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06192 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06195 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a06184 ^ 1)
theorem ha06196 : a06196.IsHomogeneous 36 := by
  unfold a06196
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06192.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06195.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha06184.pow 1)))

@[irreducible]
def a06197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06194 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06196 ^ 1)
theorem ha06197 : a06197.IsHomogeneous 36 := by
  unfold a06197
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06194.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06185.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06196.pow 1)))

@[irreducible]
def a06198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1)
theorem ha06198 : a06198.IsHomogeneous 12 := by
  unfold a06198
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a06199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06189 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06198 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06193 ^ 1)
theorem ha06199 : a06199.IsHomogeneous 18 := by
  unfold a06199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06189.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06198.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06193.pow 1)))

@[irreducible]
def a06200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06194 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06199 ^ 1)
theorem ha06200 : a06200.IsHomogeneous 24 := by
  unfold a06200
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06194.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06199.pow 1)))

@[irreducible]
def a06201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06197 ^ 1)
theorem ha06201 : a06201.IsHomogeneous 36 := by
  unfold a06201
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06200.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06191.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06197.pow 1)))

@[irreducible]
def a06202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00506 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00547 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00547 ^ 1)
theorem ha06202 : a06202.IsHomogeneous 36 := by
  unfold a06202
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01412.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a06203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a01327 ^ 1)
theorem ha06203 : a06203.IsHomogeneous 30 := by
  unfold a06203
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06203 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a06202 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a06182 ^ 1)
theorem ha06204 : a06204.IsHomogeneous 36 := by
  unfold a06204
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha06202.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha06182.pow 1)))

@[irreducible]
def a06205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a01412 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a01412 ^ 1)
theorem ha06205 : a06205.IsHomogeneous 30 := by
  unfold a06205
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha03085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a06206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06205 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06184 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06202 ^ 1)
theorem ha06206 : a06206.IsHomogeneous 36 := by
  unfold a06206
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06184.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06202.pow 1)))

@[irreducible]
def a06207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06185 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06206 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a06204 ^ 1)
theorem ha06207 : a06207.IsHomogeneous 36 := by
  unfold a06207
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06206.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha06204.pow 1)))

@[irreducible]
def a06208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a05754 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02935 ^ 1)
theorem ha06208 : a06208.IsHomogeneous 24 := by
  unfold a06208
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06187 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a06208 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06203 ^ 1)
theorem ha06209 : a06209.IsHomogeneous 30 := by
  unfold a06209
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06187.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha06208.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06203.pow 1)))

@[irreducible]
def a06210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06209 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06204 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a06188 ^ 1)
theorem ha06210 : a06210.IsHomogeneous 36 := by
  unfold a06210
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06204.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha06188.pow 1)))

@[irreducible]
def a06211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06207 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06210 ^ 1)
theorem ha06211 : a06211.IsHomogeneous 36 := by
  unfold a06211
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06191.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06207.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06210.pow 1)))

@[irreducible]
def a06212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a03085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05994 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1)
theorem ha06212 : a06212.IsHomogeneous 24 := by
  unfold a06212
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05994.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a06213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06195 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06212 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06205 ^ 1)
theorem ha06213 : a06213.IsHomogeneous 30 := by
  unfold a06213
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06195.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06212.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06205.pow 1)))

@[irreducible]
def a06214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06213 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06206 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a06196 ^ 1)
theorem ha06214 : a06214.IsHomogeneous 36 := by
  unfold a06214
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06206.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha06196.pow 1)))

@[irreducible]
def a06215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06207 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a06214 ^ 1)
theorem ha06215 : a06215.IsHomogeneous 36 := by
  unfold a06215
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06197.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06207.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha06214.pow 1)))

@[irreducible]
def a06216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06215 ^ 1)
theorem ha06216 : a06216.IsHomogeneous 36 := by
  unfold a06216
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06201.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06211.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06215.pow 1)))

@[irreducible]
def a06217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a05839 ^ 1) + (C ((7 : ℂ) / (6480 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a06216 ^ 1)
theorem ha06217 : a06217.IsHomogeneous 51 := by
  unfold a06217
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha05839.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6480 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha06216.pow 1)))

@[irreducible]
def a06218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00506 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a00506 ^ 1)
theorem ha06218 : a06218.IsHomogeneous 36 := by
  unfold a06218
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha01327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00171 ^ 1)
theorem ha06219 : a06219.IsHomogeneous 30 := by
  unfold a06219
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a06220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a01429 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha06220 : a06220.IsHomogeneous 30 := by
  unfold a06220
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06220 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a06218 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06219 ^ 1)
theorem ha06221 : a06221.IsHomogeneous 36 := by
  unfold a06221
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06220.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha06218.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06219.pow 1)))

@[irreducible]
def a06222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00506 ^ 1)
theorem ha06222 : a06222.IsHomogeneous 30 := by
  unfold a06222
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a01327 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a01327 ^ 1)
theorem ha06223 : a06223.IsHomogeneous 24 := by
  unfold a06223
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06223 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a06218 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06222 ^ 1)
theorem ha06224 : a06224.IsHomogeneous 36 := by
  unfold a06224
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha06218.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06222.pow 1)))

@[irreducible]
def a06225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00171 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1)
theorem ha06225 : a06225.IsHomogeneous 18 := by
  unfold a06225
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a06226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06225 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06219 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a06222 ^ 1)
theorem ha06226 : a06226.IsHomogeneous 30 := by
  unfold a06226
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06219.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha06222.pow 1)))

@[irreducible]
def a06227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06226 ^ 1) + (C ((5 : ℂ) / (84 : ℂ)) * a06221 ^ 1) + (C ((5 : ℂ) / (504 : ℂ)) * a06224 ^ 1)
theorem ha06227 : a06227.IsHomogeneous 36 := by
  unfold a06227
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06226.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (84 : ℂ))).mul (ha06221.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (504 : ℂ))).mul (ha06224.pow 1)))

@[irreducible]
def a06228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00555 ^ 1)
theorem ha06228 : a06228.IsHomogeneous 24 := by
  unfold a06228
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00171 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00555 ^ 1)
theorem ha06229 : a06229.IsHomogeneous 18 := by
  unfold a06229
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1)))

@[irreducible]
def a06230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06219 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06229 ^ 1)
theorem ha06230 : a06230.IsHomogeneous 30 := by
  unfold a06230
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06228.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06219.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06229.pow 1)))

@[irreducible]
def a06231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha06231 : a06231.IsHomogeneous 24 := by
  unfold a06231
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a06232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06228 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a06231 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06220 ^ 1)
theorem ha06232 : a06232.IsHomogeneous 30 := by
  unfold a06232
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha06231.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06220.pow 1)))

@[irreducible]
def a06233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06230 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06221 ^ 1)
theorem ha06233 : a06233.IsHomogeneous 36 := by
  unfold a06233
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06230.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06221.pow 1)))

@[irreducible]
def a06234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00171 ^ 1)
theorem ha06234 : a06234.IsHomogeneous 12 := by
  unfold a06234
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)))

@[irreducible]
def a06235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06225 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06229 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a06234 ^ 1)
theorem ha06235 : a06235.IsHomogeneous 18 := by
  unfold a06235
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06229.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha06234.pow 1)))

@[irreducible]
def a06236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06235 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06226 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06230 ^ 1)
theorem ha06236 : a06236.IsHomogeneous 30 := by
  unfold a06236
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06235.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06226.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06230.pow 1)))

@[irreducible]
def a06237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06227 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06233 ^ 1)
theorem ha06237 : a06237.IsHomogeneous 36 := by
  unfold a06237
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06236.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06227.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06233.pow 1)))

@[irreducible]
def a06238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a01327 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a00555 ^ 1)
theorem ha06238 : a06238.IsHomogeneous 30 := by
  unfold a06238
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a01327 ^ 1)
theorem ha06239 : a06239.IsHomogeneous 30 := by
  unfold a06239
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06238 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06239 ^ 1) + (C ((1 : ℂ) / (30 : ℂ)) * a06218 ^ 1)
theorem ha06240 : a06240.IsHomogeneous 36 := by
  unfold a06240
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06239.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (30 : ℂ))).mul (ha06218.pow 1)))

@[irreducible]
def a06241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a01429 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a01429 ^ 1)
theorem ha06241 : a06241.IsHomogeneous 30 := by
  unfold a06241
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha03116.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a06242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06220 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06241 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a06238 ^ 1)
theorem ha06242 : a06242.IsHomogeneous 30 := by
  unfold a06242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06220.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06241.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha06238.pow 1)))

@[irreducible]
def a06243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06221 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a06240 ^ 1)
theorem ha06243 : a06243.IsHomogeneous 36 := by
  unfold a06243
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06221.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha06240.pow 1)))

@[irreducible]
def a06244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02935 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a02935 ^ 1)
theorem ha06244 : a06244.IsHomogeneous 24 := by
  unfold a06244
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06223 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06244 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06239 ^ 1)
theorem ha06245 : a06245.IsHomogeneous 30 := by
  unfold a06245
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06244.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06239.pow 1)))

@[irreducible]
def a06246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06245 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06224 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a06240 ^ 1)
theorem ha06246 : a06246.IsHomogeneous 36 := by
  unfold a06246
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06245.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06224.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha06240.pow 1)))

@[irreducible]
def a06247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06227 ^ 1) + (C ((5 : ℂ) / (84 : ℂ)) * a06243 ^ 1) + (C ((5 : ℂ) / (504 : ℂ)) * a06246 ^ 1)
theorem ha06247 : a06247.IsHomogeneous 36 := by
  unfold a06247
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (84 : ℂ))).mul (ha06243.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (504 : ℂ))).mul (ha06246.pow 1)))

@[irreducible]
def a06248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a03116 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06044 ^ 1)
theorem ha06248 : a06248.IsHomogeneous 24 := by
  unfold a06248
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06044.pow 1)))

@[irreducible]
def a06249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06231 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06248 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a06241 ^ 1)
theorem ha06249 : a06249.IsHomogeneous 30 := by
  unfold a06249
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06231.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06248.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha06241.pow 1)))

@[irreducible]
def a06250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06232 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06242 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06249 ^ 1)
theorem ha06250 : a06250.IsHomogeneous 30 := by
  unfold a06250
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06242.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06249.pow 1)))

@[irreducible]
def a06251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06233 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a06243 ^ 1)
theorem ha06251 : a06251.IsHomogeneous 36 := by
  unfold a06251
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06233.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha06243.pow 1)))

@[irreducible]
def a06252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06247 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06251 ^ 1)
theorem ha06252 : a06252.IsHomogeneous 36 := by
  unfold a06252
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06247.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06251.pow 1)))

@[irreducible]
def a06253 : Poly := (C ((-7 : ℂ) / (1080 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00004 ^ 3 * a00005 ^ 1 * a06252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06181 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a06217 ^ 1)
theorem ha06253 : a06253.IsHomogeneous 57 := by
  unfold a06253
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (1080 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha06252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06181.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha06217.pow 1)))

@[irreducible]
def a06254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a01473 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00577 ^ 1 * a00864 ^ 1)
theorem ha06254 : a06254.IsHomogeneous 36 := by
  unfold a06254
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha01473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00577.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00577 ^ 1 * a00864 ^ 1)
theorem ha06255 : a06255.IsHomogeneous 36 := by
  unfold a06255
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00577.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06255 ^ 1)
theorem ha06256 : a06256.IsHomogeneous 36 := by
  unfold a06256
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06254.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06255.pow 1)))

@[irreducible]
def a06257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01473 ^ 1)
theorem ha06257 : a06257.IsHomogeneous 30 := by
  unfold a06257
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a06258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06257 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06254 ^ 1)
theorem ha06258 : a06258.IsHomogeneous 36 := by
  unfold a06258
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06254.pow 1)))

@[irreducible]
def a06259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06258 ^ 1)
theorem ha06259 : a06259.IsHomogeneous 36 := by
  unfold a06259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06258.pow 1)))

@[irreducible]
def a06260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a02007 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a04085 ^ 1)
theorem ha06260 : a06260.IsHomogeneous 30 := by
  unfold a06260
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a06261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06255 ^ 1)
theorem ha06261 : a06261.IsHomogeneous 36 := by
  unfold a06261
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06255.pow 1)))

@[irreducible]
def a06262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06261 ^ 1)
theorem ha06262 : a06262.IsHomogeneous 36 := by
  unfold a06262
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06261.pow 1)))

@[irreducible]
def a06263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06262 ^ 1)
theorem ha06263 : a06263.IsHomogeneous 36 := by
  unfold a06263
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06262.pow 1)))

@[irreducible]
def a06264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06158 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03191 ^ 1)
theorem ha06264 : a06264.IsHomogeneous 24 := by
  unfold a06264
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03191.pow 1)))

@[irreducible]
def a06265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06257 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a06264 ^ 1)
theorem ha06265 : a06265.IsHomogeneous 30 := by
  unfold a06265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06257.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha06264.pow 1)))

@[irreducible]
def a06266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06265 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06258 ^ 1)
theorem ha06266 : a06266.IsHomogeneous 36 := by
  unfold a06266
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06258.pow 1)))

@[irreducible]
def a06267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06266 ^ 1)
theorem ha06267 : a06267.IsHomogeneous 36 := by
  unfold a06267
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06266.pow 1)))

@[irreducible]
def a06268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06263 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06267 ^ 1)
theorem ha06268 : a06268.IsHomogeneous 36 := by
  unfold a06268
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06263.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06267.pow 1)))

@[irreducible]
def a06269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00528 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01373 ^ 1)
theorem ha06269 : a06269.IsHomogeneous 45 := by
  unfold a06269
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00528.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a06270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a03016 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a01373 ^ 1)
theorem ha06270 : a06270.IsHomogeneous 45 := by
  unfold a06270
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a06271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06269 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06270 ^ 1)
theorem ha06271 : a06271.IsHomogeneous 45 := by
  unfold a06271
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06270.pow 1)))

@[irreducible]
def a06272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a02008 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00528 ^ 1 * a00865 ^ 1)
theorem ha06272 : a06272.IsHomogeneous 42 := by
  unfold a06272
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00528.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06272 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06269 ^ 1)
theorem ha06273 : a06273.IsHomogeneous 48 := by
  unfold a06273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06272.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06269.pow 1)))

@[irreducible]
def a06274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06273 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a06271 ^ 1)
theorem ha06274 : a06274.IsHomogeneous 48 := by
  unfold a06274
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06273.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha06271.pow 1)))

@[irreducible]
def a06275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a05883 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03016 ^ 1)
theorem ha06275 : a06275.IsHomogeneous 48 := by
  unfold a06275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha05883.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03016.pow 1)))

@[irreducible]
def a06276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06275 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06270 ^ 1)
theorem ha06276 : a06276.IsHomogeneous 48 := by
  unfold a06276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06270.pow 1)))

@[irreducible]
def a06277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06276 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06271 ^ 1)
theorem ha06277 : a06277.IsHomogeneous 48 := by
  unfold a06277
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06276.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06271.pow 1)))

@[irreducible]
def a06278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06274 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a06277 ^ 1)
theorem ha06278 : a06278.IsHomogeneous 48 := by
  unfold a06278
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06274.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha06277.pow 1)))

@[irreducible]
def a06279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a04086 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a02008 ^ 1)
theorem ha06279 : a06279.IsHomogeneous 36 := by
  unfold a06279
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06272 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a06279 ^ 1)
theorem ha06280 : a06280.IsHomogeneous 42 := by
  unfold a06280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06272.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha06279.pow 1)))

@[irreducible]
def a06281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06273 ^ 1)
theorem ha06281 : a06281.IsHomogeneous 48 := by
  unfold a06281
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06273.pow 1)))

@[irreducible]
def a06282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06274 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06281 ^ 1)
theorem ha06282 : a06282.IsHomogeneous 48 := by
  unfold a06282
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06274.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06281.pow 1)))

@[irreducible]
def a06283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06282 ^ 1)
theorem ha06283 : a06283.IsHomogeneous 48 := by
  unfold a06283
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06282.pow 1)))

@[irreducible]
def a06284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a06283 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a06268 ^ 1)
theorem ha06284 : a06284.IsHomogeneous 54 := by
  unfold a06284
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha06283.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha06268.pow 1)))

@[irreducible]
def a06285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05888 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a06268 ^ 1)
theorem ha06285 : a06285.IsHomogeneous 36 := by
  unfold a06285
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha06268.pow 1)))

@[irreducible]
def a06286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06284 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a06285 ^ 1)
theorem ha06286 : a06286.IsHomogeneous 54 := by
  unfold a06286
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06284.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha06285.pow 1)))

@[irreducible]
def a06287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a06283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06284 ^ 1)
theorem ha06287 : a06287.IsHomogeneous 54 := by
  unfold a06287
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha06283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06284.pow 1)))

@[irreducible]
def a06288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06287 ^ 1)
theorem ha06288 : a06288.IsHomogeneous 54 := by
  unfold a06288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06287.pow 1)))

@[irreducible]
def a06289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00520 ^ 1)
theorem ha06289 : a06289.IsHomogeneous 33 := by
  unfold a06289
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a06290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00129 ^ 1 * a00520 ^ 1)
theorem ha06290 : a06290.IsHomogeneous 45 := by
  unfold a06290
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a06291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00317 ^ 1)
theorem ha06291 : a06291.IsHomogeneous 39 := by
  unfold a06291
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06290 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06289 ^ 1)
theorem ha06292 : a06292.IsHomogeneous 45 := by
  unfold a06292
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06290.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06289.pow 1)))

@[irreducible]
def a06293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a01356 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00520 ^ 1)
theorem ha06293 : a06293.IsHomogeneous 42 := by
  unfold a06293
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a06294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1)
theorem ha06294 : a06294.IsHomogeneous 36 := by
  unfold a06294
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06293 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06289 ^ 1)
theorem ha06295 : a06295.IsHomogeneous 42 := by
  unfold a06295
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06294.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06293.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06289.pow 1)))

@[irreducible]
def a06296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01356 ^ 1)
theorem ha06296 : a06296.IsHomogeneous 48 := by
  unfold a06296
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a06297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06296 ^ 1) + (C ((35 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06293 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06290 ^ 1)
theorem ha06297 : a06297.IsHomogeneous 48 := by
  unfold a06297
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06296.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06293.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06290.pow 1)))

@[irreducible]
def a06298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06297 ^ 1) + (C ((35 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06295 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06292 ^ 1)
theorem ha06298 : a06298.IsHomogeneous 48 := by
  unfold a06298
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06297.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06295.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06292.pow 1)))

@[irreducible]
def a06299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00317 ^ 1)
theorem ha06299 : a06299.IsHomogeneous 33 := by
  unfold a06299
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a06300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00129 ^ 1)
theorem ha06300 : a06300.IsHomogeneous 33 := by
  unfold a06300
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a06301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06299 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06300 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06289 ^ 1)
theorem ha06301 : a06301.IsHomogeneous 39 := by
  unfold a06301
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06300.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06289.pow 1)))

@[irreducible]
def a06302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00020 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1)
theorem ha06302 : a06302.IsHomogeneous 36 := by
  unfold a06302
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06302 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06291 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06299 ^ 1)
theorem ha06303 : a06303.IsHomogeneous 42 := by
  unfold a06303
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06291.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06299.pow 1)))

@[irreducible]
def a06304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06303 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06292 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06301 ^ 1)
theorem ha06304 : a06304.IsHomogeneous 48 := by
  unfold a06304
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06303.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06292.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06301.pow 1)))

@[irreducible]
def a06305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00042 ^ 1)
theorem ha06305 : a06305.IsHomogeneous 36 := by
  unfold a06305
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a06306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06305 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06300 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06294 ^ 1)
theorem ha06306 : a06306.IsHomogeneous 42 := by
  unfold a06306
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06305.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06300.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06294.pow 1)))

@[irreducible]
def a06307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06306 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06301 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06295 ^ 1)
theorem ha06307 : a06307.IsHomogeneous 48 := by
  unfold a06307
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06306.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06301.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06295.pow 1)))

@[irreducible]
def a06308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06298 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06304 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a06307 ^ 1)
theorem ha06308 : a06308.IsHomogeneous 48 := by
  unfold a06308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06304.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha06307.pow 1)))

@[irreducible]
def a06309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00520 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1 * a00520 ^ 1)
theorem ha06309 : a06309.IsHomogeneous 45 := by
  unfold a06309
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a06310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a01356 ^ 1)
theorem ha06310 : a06310.IsHomogeneous 45 := by
  unfold a06310
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a06311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06290 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06309 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a06310 ^ 1)
theorem ha06311 : a06311.IsHomogeneous 45 := by
  unfold a06311
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06309.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha06310.pow 1)))

@[irreducible]
def a06312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00865 ^ 1)
theorem ha06312 : a06312.IsHomogeneous 39 := by
  unfold a06312
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a06313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06291 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06312 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06309 ^ 1)
theorem ha06313 : a06313.IsHomogeneous 45 := by
  unfold a06313
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06291.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06312.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06309.pow 1)))

@[irreducible]
def a06314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06311 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06313 ^ 1)
theorem ha06314 : a06314.IsHomogeneous 45 := by
  unfold a06314
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06311.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06313.pow 1)))

@[irreducible]
def a06315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a05834 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a02985 ^ 1)
theorem ha06315 : a06315.IsHomogeneous 48 := by
  unfold a06315
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a06316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06296 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06315 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06310 ^ 1)
theorem ha06316 : a06316.IsHomogeneous 48 := by
  unfold a06316
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06296.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06315.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06310.pow 1)))

@[irreducible]
def a06317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06297 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06316 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06311 ^ 1)
theorem ha06317 : a06317.IsHomogeneous 48 := by
  unfold a06317
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06297.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06311.pow 1)))

@[irreducible]
def a06318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06317 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06314 ^ 1)
theorem ha06318 : a06318.IsHomogeneous 48 := by
  unfold a06318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06314.pow 1)))

@[irreducible]
def a06319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a02008 ^ 1)
theorem ha06319 : a06319.IsHomogeneous 36 := by
  unfold a06319
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04086.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a06320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06302 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a06319 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06312 ^ 1)
theorem ha06320 : a06320.IsHomogeneous 42 := by
  unfold a06320
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06302.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha06319.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06312.pow 1)))

@[irreducible]
def a06321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06303 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06320 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06313 ^ 1)
theorem ha06321 : a06321.IsHomogeneous 48 := by
  unfold a06321
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06303.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06320.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06313.pow 1)))

@[irreducible]
def a06322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06321 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06314 ^ 1)
theorem ha06322 : a06322.IsHomogeneous 48 := by
  unfold a06322
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06304.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06321.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06314.pow 1)))

@[irreducible]
def a06323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06318 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06322 ^ 1)
theorem ha06323 : a06323.IsHomogeneous 48 := by
  unfold a06323
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06308.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06318.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06322.pow 1)))

@[irreducible]
def a06324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a06323 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a05999 ^ 1)
theorem ha06324 : a06324.IsHomogeneous 54 := by
  unfold a06324
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha06323.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha05999.pow 1)))

@[irreducible]
def a06325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06324 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a06000 ^ 1)
theorem ha06325 : a06325.IsHomogeneous 54 := by
  unfold a06325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06324.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha06000.pow 1)))

@[irreducible]
def a06326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha06326 : a06326.IsHomogeneous 45 := by
  unfold a06326
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a06327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00316 ^ 1)
theorem ha06327 : a06327.IsHomogeneous 33 := by
  unfold a06327
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a06328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00621 ^ 1)
theorem ha06328 : a06328.IsHomogeneous 39 := by
  unfold a06328
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06326 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06327 ^ 1)
theorem ha06329 : a06329.IsHomogeneous 45 := by
  unfold a06329
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06326.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06327.pow 1)))

@[irreducible]
def a06330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a00864 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha06330 : a06330.IsHomogeneous 42 := by
  unfold a06330
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a06331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a00201 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00054 ^ 1 * a00864 ^ 1)
theorem ha06331 : a06331.IsHomogeneous 48 := by
  unfold a06331
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06331 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06326 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06330 ^ 1)
theorem ha06332 : a06332.IsHomogeneous 48 := by
  unfold a06332
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06331.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06326.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06330.pow 1)))

@[irreducible]
def a06333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha06333 : a06333.IsHomogeneous 36 := by
  unfold a06333
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a06334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06330 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06327 ^ 1)
theorem ha06334 : a06334.IsHomogeneous 42 := by
  unfold a06334
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06327.pow 1)))

@[irreducible]
def a06335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06332 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06329 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06334 ^ 1)
theorem ha06335 : a06335.IsHomogeneous 48 := by
  unfold a06335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06332.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06329.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06334.pow 1)))

@[irreducible]
def a06336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a01555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00621 ^ 1)
theorem ha06336 : a06336.IsHomogeneous 33 := by
  unfold a06336
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha01555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00621.pow 1)))

@[irreducible]
def a06337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00201 ^ 1)
theorem ha06337 : a06337.IsHomogeneous 33 := by
  unfold a06337
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)))

@[irreducible]
def a06338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06336 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06337 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a06327 ^ 1)
theorem ha06338 : a06338.IsHomogeneous 39 := by
  unfold a06338
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06336.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06337.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha06327.pow 1)))

@[irreducible]
def a06339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01555 ^ 1)
theorem ha06339 : a06339.IsHomogeneous 36 := by
  unfold a06339
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a06340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06339 ^ 1) + (C ((35 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06336 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06328 ^ 1)
theorem ha06340 : a06340.IsHomogeneous 42 := by
  unfold a06340
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06339.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06336.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06328.pow 1)))

@[irreducible]
def a06341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06340 ^ 1) + (C ((35 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06338 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06329 ^ 1)
theorem ha06341 : a06341.IsHomogeneous 48 := by
  unfold a06341
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06340.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06338.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06329.pow 1)))

@[irreducible]
def a06342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00054 ^ 1)
theorem ha06342 : a06342.IsHomogeneous 36 := by
  unfold a06342
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)))

@[irreducible]
def a06343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06342 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06337 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06333 ^ 1)
theorem ha06343 : a06343.IsHomogeneous 42 := by
  unfold a06343
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06342.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06337.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06333.pow 1)))

@[irreducible]
def a06344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06343 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06338 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06334 ^ 1)
theorem ha06344 : a06344.IsHomogeneous 48 := by
  unfold a06344
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06343.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06338.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06334.pow 1)))

@[irreducible]
def a06345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06335 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06341 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a06344 ^ 1)
theorem ha06345 : a06345.IsHomogeneous 48 := by
  unfold a06345
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06341.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha06344.pow 1)))

@[irreducible]
def a06346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a00621 ^ 1)
theorem ha06346 : a06346.IsHomogeneous 45 := by
  unfold a06346
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a06347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00621 ^ 1 * a00864 ^ 1)
theorem ha06347 : a06347.IsHomogeneous 45 := by
  unfold a06347
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00621.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06326 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a06347 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06346 ^ 1)
theorem ha06348 : a06348.IsHomogeneous 45 := by
  unfold a06348
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha06347.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06346.pow 1)))

@[irreducible]
def a06349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a03330 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1)
theorem ha06349 : a06349.IsHomogeneous 39 := by
  unfold a06349
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a06350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06328 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a06349 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a06346 ^ 1)
theorem ha06350 : a06350.IsHomogeneous 45 := by
  unfold a06350
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06328.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha06349.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha06346.pow 1)))

@[irreducible]
def a06351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06350 ^ 1)
theorem ha06351 : a06351.IsHomogeneous 45 := by
  unfold a06351
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06348.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06350.pow 1)))

@[irreducible]
def a06352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a04085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a02007 ^ 1)
theorem ha06352 : a06352.IsHomogeneous 48 := by
  unfold a06352
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a06353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06331 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06352 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06347 ^ 1)
theorem ha06353 : a06353.IsHomogeneous 48 := by
  unfold a06353
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06331.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06352.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06347.pow 1)))

@[irreducible]
def a06354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06353 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06348 ^ 1)
theorem ha06354 : a06354.IsHomogeneous 48 := by
  unfold a06354
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06353.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06348.pow 1)))

@[irreducible]
def a06355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06354 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06351 ^ 1)
theorem ha06355 : a06355.IsHomogeneous 48 := by
  unfold a06355
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06354.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06351.pow 1)))

@[irreducible]
def a06356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1)
theorem ha06356 : a06356.IsHomogeneous 21 := by
  unfold a06356
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)))

@[irreducible]
def a06357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00317 ^ 1)
theorem ha06357 : a06357.IsHomogeneous 21 := by
  unfold a06357
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a06358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06356 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a06357 ^ 1)
theorem ha06358 : a06358.IsHomogeneous 21 := by
  unfold a06358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06356.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha06357.pow 1)))

@[irreducible]
def a06359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02720 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06357 ^ 1)
theorem ha06359 : a06359.IsHomogeneous 24 := by
  unfold a06359
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02720.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06357.pow 1)))

@[irreducible]
def a06360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06359 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06358 ^ 1)
theorem ha06360 : a06360.IsHomogeneous 24 := by
  unfold a06360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06359.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06358.pow 1)))

@[irreducible]
def a06361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a02008 ^ 1)
theorem ha06361 : a06361.IsHomogeneous 21 := by
  unfold a06361
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha02008.pow 1)))

@[irreducible]
def a06362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06356 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06361 ^ 1)
theorem ha06362 : a06362.IsHomogeneous 21 := by
  unfold a06362
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06356.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06361.pow 1)))

@[irreducible]
def a06363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06358 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06362 ^ 1)
theorem ha06363 : a06363.IsHomogeneous 21 := by
  unfold a06363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06362.pow 1)))

@[irreducible]
def a06364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06360 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06363 ^ 1)
theorem ha06364 : a06364.IsHomogeneous 24 := by
  unfold a06364
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06360.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06363.pow 1)))

@[irreducible]
def a06365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02008 ^ 1)
theorem ha06365 : a06365.IsHomogeneous 24 := by
  unfold a06365
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02008.pow 1)))

@[irreducible]
def a06366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06365 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06361 ^ 1)
theorem ha06366 : a06366.IsHomogeneous 24 := by
  unfold a06366
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06365.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06361.pow 1)))

@[irreducible]
def a06367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06366 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06362 ^ 1)
theorem ha06367 : a06367.IsHomogeneous 24 := by
  unfold a06367
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06366.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06362.pow 1)))

@[irreducible]
def a06368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06367 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06363 ^ 1)
theorem ha06368 : a06368.IsHomogeneous 24 := by
  unfold a06368
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06367.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06363.pow 1)))

@[irreducible]
def a06369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06364 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06368 ^ 1)
theorem ha06369 : a06369.IsHomogeneous 24 := by
  unfold a06369
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06368.pow 1)))

@[irreducible]
def a06370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03183 ^ 1) + (C ((7 : ℂ) / (24 : ℂ)) * a03357 ^ 1)
theorem ha06370 : a06370.IsHomogeneous 6 := by
  unfold a06370
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (24 : ℂ))).mul (ha03357.pow 1)))

@[irreducible]
def a06371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03358 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a06370 ^ 1)
theorem ha06371 : a06371.IsHomogeneous 6 := by
  unfold a06371
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha06370.pow 1)))

@[irreducible]
def a06372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06371 ^ 1)
theorem ha06372 : a06372.IsHomogeneous 6 := by
  unfold a06372
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06371.pow 1)))

@[irreducible]
def a06373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06370 ^ 1)
theorem ha06373 : a06373.IsHomogeneous 6 := by
  unfold a06373
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06370.pow 1)))

@[irreducible]
def a06374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06371 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a06373 ^ 1)
theorem ha06374 : a06374.IsHomogeneous 6 := by
  unfold a06374
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha06373.pow 1)))

@[irreducible]
def a06375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06374 ^ 1)
theorem ha06375 : a06375.IsHomogeneous 6 := by
  unfold a06375
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06372.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06374.pow 1)))

@[irreducible]
def a06376 : Poly := (C ((-7 : ℂ) / (324 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06369 ^ 1)
theorem ha06376 : a06376.IsHomogeneous 24 := by
  unfold a06376
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (324 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06375.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06369.pow 1)))

@[irreducible]
def a06377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a06376 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a03330 ^ 1)
theorem ha06377 : a06377.IsHomogeneous 36 := by
  unfold a06377
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a06378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06339 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a06377 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06349 ^ 1)
theorem ha06378 : a06378.IsHomogeneous 42 := by
  unfold a06378
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06339.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha06377.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06349.pow 1)))

@[irreducible]
def a06379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06378 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06350 ^ 1)
theorem ha06379 : a06379.IsHomogeneous 48 := by
  unfold a06379
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06378.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06350.pow 1)))

@[irreducible]
def a06380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06379 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a06351 ^ 1)
theorem ha06380 : a06380.IsHomogeneous 48 := by
  unfold a06380
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06341.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06379.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha06351.pow 1)))

@[irreducible]
def a06381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06345 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06355 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06380 ^ 1)
theorem ha06381 : a06381.IsHomogeneous 48 := by
  unfold a06381
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06355.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06380.pow 1)))

@[irreducible]
def a06382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a06381 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a05939 ^ 1)
theorem ha06382 : a06382.IsHomogeneous 54 := by
  unfold a06382
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha06381.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha05939.pow 1)))

@[irreducible]
def a06383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06382 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a06000 ^ 1)
theorem ha06383 : a06383.IsHomogeneous 54 := by
  unfold a06383
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06382.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha06000.pow 1)))

@[irreducible]
def a06384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06325 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06383 ^ 1)
theorem ha06384 : a06384.IsHomogeneous 54 := by
  unfold a06384
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06383.pow 1)))

@[irreducible]
def a06385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a00632 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00864 ^ 1)
theorem ha06385 : a06385.IsHomogeneous 30 := by
  unfold a06385
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00207 ^ 1)
theorem ha06386 : a06386.IsHomogeneous 24 := by
  unfold a06386
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a06387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00316 ^ 1 * a00632 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1)
theorem ha06387 : a06387.IsHomogeneous 24 := by
  unfold a06387
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06386 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06387 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06385 ^ 1)
theorem ha06388 : a06388.IsHomogeneous 30 := by
  unfold a06388
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06386.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06387.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06385.pow 1)))

@[irreducible]
def a06389 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00058 ^ 1 * a00316 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00316 ^ 1 * a00324 ^ 1)
theorem ha06389 : a06389.IsHomogeneous 30 := by
  unfold a06389
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a06390 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00864 ^ 1)
theorem ha06390 : a06390.IsHomogeneous 30 := by
  unfold a06390
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06391 : Poly := (C ((-1 : ℂ) / (14 : ℂ)) * a06390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06385 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06389 ^ 1)
theorem ha06391 : a06391.IsHomogeneous 30 := by
  unfold a06391
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (14 : ℂ))).mul (ha06390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06385.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06389.pow 1)))

@[irreducible]
def a06392 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00316 ^ 1)
theorem ha06392 : a06392.IsHomogeneous 18 := by
  unfold a06392
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a06393 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06389 ^ 1)
theorem ha06393 : a06393.IsHomogeneous 30 := by
  unfold a06393
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06386.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06389.pow 1)))

@[irreducible]
def a06394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06393 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06391 ^ 1)
theorem ha06394 : a06394.IsHomogeneous 30 := by
  unfold a06394
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06393.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06391.pow 1)))

@[irreducible]
def a06395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00632 ^ 1)
theorem ha06395 : a06395.IsHomogeneous 18 := by
  unfold a06395
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a06396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00207 ^ 1)
theorem ha06396 : a06396.IsHomogeneous 18 := by
  unfold a06396
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)))

@[irreducible]
def a06397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06386 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06396 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06395 ^ 1)
theorem ha06397 : a06397.IsHomogeneous 24 := by
  unfold a06397
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06386.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06396.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06395.pow 1)))

@[irreducible]
def a06398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha06398 : a06398.IsHomogeneous 18 := by
  unfold a06398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a06399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06387 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06398 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a06395 ^ 1)
theorem ha06399 : a06399.IsHomogeneous 24 := by
  unfold a06399
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06398.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha06395.pow 1)))

end CycleQ2Concrete
