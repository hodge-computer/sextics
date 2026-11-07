import Proposal.CurrentAtoms020

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a07168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07167 ^ 1)
theorem ha07168 : a07168.IsHomogeneous 485 := by
  unfold a07168
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07167.pow 1)))

@[irreducible]
def a07169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a03764 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00773 ^ 1 * a01822 ^ 1)
theorem ha07169 : a07169.IsHomogeneous 191 := by
  unfold a07169
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha03764.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00773.pow 1)).mul (ha01822.pow 1)))

@[irreducible]
def a07170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00773 ^ 1 * a01822 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07169 ^ 1)
theorem ha07170 : a07170.IsHomogeneous 191 := by
  unfold a07170
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00773.pow 1)).mul (ha01822.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07169.pow 1)))

@[irreducible]
def a07171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07048 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00285 ^ 1 * a03764 ^ 1)
theorem ha07171 : a07171.IsHomogeneous 191 := by
  unfold a07171
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00285.pow 1)).mul (ha03764.pow 1)))

@[irreducible]
def a07172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07169 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a07171 ^ 1)
theorem ha07172 : a07172.IsHomogeneous 191 := by
  unfold a07172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha07171.pow 1)))

@[irreducible]
def a07173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07170 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07172 ^ 1)
theorem ha07173 : a07173.IsHomogeneous 191 := by
  unfold a07173
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07172.pow 1)))

@[irreducible]
def a07174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07170 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07173 ^ 1)
theorem ha07174 : a07174.IsHomogeneous 191 := by
  unfold a07174
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07173.pow 1)))

@[irreducible]
def a07175 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a03837 ^ 1)
theorem ha07175 : a07175.IsHomogeneous 289 := by
  unfold a07175
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07174.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha03837.pow 1)))

@[irreducible]
def a07176 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07175 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07154 ^ 1)
theorem ha07176 : a07176.IsHomogeneous 387 := by
  unfold a07176
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07154.pow 1)))

@[irreducible]
def a07177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07155 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07176 ^ 1)
theorem ha07177 : a07177.IsHomogeneous 485 := by
  unfold a07177
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07176.pow 1)))

@[irreducible]
def a07178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07177 ^ 1)
theorem ha07178 : a07178.IsHomogeneous 485 := by
  unfold a07178
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07177.pow 1)))

@[irreducible]
def a07179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00290 ^ 1 * a03840 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a07178 ^ 1)
theorem ha07179 : a07179.IsHomogeneous 606 := by
  unfold a07179
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00290.pow 1)).mul (ha03840.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07178.pow 1)))

@[irreducible]
def a07180 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a07179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07086 ^ 1)
theorem ha07180 : a07180.IsHomogeneous 667 := by
  unfold a07180
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07179.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07086.pow 1)))

@[irreducible]
def a07181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07087 ^ 1)
theorem ha07181 : a07181.IsHomogeneous 673 := by
  unfold a07181
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07087.pow 1)))

@[irreducible]
def a07182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07088 ^ 1)
theorem ha07182 : a07182.IsHomogeneous 679 := by
  unfold a07182
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07181.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07088.pow 1)))

@[irreducible]
def a07183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07152 ^ 1)
theorem ha07183 : a07183.IsHomogeneous 685 := by
  unfold a07183
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07182.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07152.pow 1)))

@[irreducible]
def a07184 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a03844 ^ 1)
theorem ha07184 : a07184.IsHomogeneous 800 := by
  unfold a07184
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07183.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a07185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07068 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07184 ^ 1)
theorem ha07185 : a07185.IsHomogeneous 915 := by
  unfold a07185
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07068.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07184.pow 1)))

@[irreducible]
def a07186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07069 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07185 ^ 1)
theorem ha07186 : a07186.IsHomogeneous 1030 := by
  unfold a07186
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07069.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07185.pow 1)))

@[irreducible]
def a07187 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07082 ^ 1)
theorem ha07187 : a07187.IsHomogeneous 1090 := by
  unfold a07187
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07082.pow 1)))

@[irreducible]
def a07188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1 * a03847 ^ 1) + (C ((20 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a07187 ^ 1)
theorem ha07188 : a07188.IsHomogeneous 1156 := by
  unfold a07188
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).mul (ha03847.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha07187.pow 1)))

@[irreducible]
def a07189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06748 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a07188 ^ 1)
theorem ha07189 : a07189.IsHomogeneous 1198 := by
  unfold a07189
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06748.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha07188.pow 1)))

@[irreducible]
def a07190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06749 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a07189 ^ 1)
theorem ha07190 : a07190.IsHomogeneous 1240 := by
  unfold a07190
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06749.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha07189.pow 1)))

@[irreducible]
def a07191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a06750 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a07190 ^ 1)
theorem ha07191 : a07191.IsHomogeneous 1282 := by
  unfold a07191
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha06750.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha07190.pow 1)))

@[irreducible]
def a07192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a07066 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a07191 ^ 1)
theorem ha07192 : a07192.IsHomogeneous 1324 := by
  unfold a07192
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha07066.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha07191.pow 1)))

@[irreducible]
def a07193 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00294 ^ 1 * a03851 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a07192 ^ 1)
theorem ha07193 : a07193.IsHomogeneous 1429 := by
  unfold a07193
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00294.pow 1)).mul (ha03851.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha07192.pow 1)))

@[irreducible]
def a07194 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06740 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07193 ^ 1)
theorem ha07194 : a07194.IsHomogeneous 1429 := by
  unfold a07194
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06740.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07193.pow 1)))

@[irreducible]
def a07195 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06741 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07194 ^ 1)
theorem ha07195 : a07195.IsHomogeneous 1429 := by
  unfold a07195
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06741.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07194.pow 1)))

@[irreducible]
def a07196 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07195 ^ 1)
theorem ha07196 : a07196.IsHomogeneous 1429 := by
  unfold a07196
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06744.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07195.pow 1)))

@[irreducible]
def a07197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00798 ^ 1 * a01702 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00712 ^ 1 * a01877 ^ 1)
theorem ha07197 : a07197.IsHomogeneous 131 := by
  unfold a07197
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00798.pow 1)).mul (ha01702.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a07198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a01702 ^ 1) + (C ((32 : ℂ) / (135 : ℂ)) * a00014 ^ 1 * a00293 ^ 1 * a03562 ^ 1)
theorem ha07198 : a07198.IsHomogeneous 132 := by
  unfold a07198
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (135 : ℂ))).mul (ha00014.pow 1)).mul (ha00293.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07198 ^ 1)
theorem ha07199 : a07199.IsHomogeneous 132 := by
  unfold a07199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07197.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07198.pow 1)))

@[irreducible]
def a07200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a01877 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a03861 ^ 1)
theorem ha07200 : a07200.IsHomogeneous 126 := by
  unfold a07200
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha01877.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a07201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07197 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07200 ^ 1)
theorem ha07201 : a07201.IsHomogeneous 132 := by
  unfold a07201
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07197.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07200.pow 1)))

@[irreducible]
def a07202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07199 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07201 ^ 1)
theorem ha07202 : a07202.IsHomogeneous 132 := by
  unfold a07202
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07199.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07201.pow 1)))

@[irreducible]
def a07203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00125 ^ 1 * a06725 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a00293 ^ 1 * a03562 ^ 1)
theorem ha07203 : a07203.IsHomogeneous 126 := by
  unfold a07203
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha00293.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07203 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a07198 ^ 1)
theorem ha07204 : a07204.IsHomogeneous 132 := by
  unfold a07204
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha07198.pow 1)))

@[irreducible]
def a07205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07199 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a07204 ^ 1)
theorem ha07205 : a07205.IsHomogeneous 132 := by
  unfold a07205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07199.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha07204.pow 1)))

@[irreducible]
def a07206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07205 ^ 1)
theorem ha07206 : a07206.IsHomogeneous 132 := by
  unfold a07206
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07205.pow 1)))

@[irreducible]
def a07207 : Poly := (C ((-3 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a06434 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a06253 ^ 1) + (C ((-1 : ℂ) / (3072 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 4 * a06725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 3 * a00012 ^ 4 * a06050 ^ 1) + (C ((1 : ℂ) / (768 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a06692 ^ 1)
theorem ha07207 : a07207.IsHomogeneous 77 := by
  unfold a07207
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha06434.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha06253.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3072 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha06725.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 3)).mul (ha00012.pow 4)).mul (ha06050.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (768 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha06692.pow 1)))

@[irreducible]
def a07208 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a07207 ^ 1)
theorem ha07208 : a07208.IsHomogeneous 120 := by
  unfold a07208
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03861.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07207.pow 1)))

@[irreducible]
def a07209 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a07208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07200 ^ 1)
theorem ha07209 : a07209.IsHomogeneous 126 := by
  unfold a07209
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha07208.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07200.pow 1)))

@[irreducible]
def a07210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07209 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a07201 ^ 1)
theorem ha07210 : a07210.IsHomogeneous 132 := by
  unfold a07210
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha07201.pow 1)))

@[irreducible]
def a07211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07202 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a07210 ^ 1)
theorem ha07211 : a07211.IsHomogeneous 132 := by
  unfold a07211
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha07210.pow 1)))

@[irreducible]
def a07212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07206 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07211 ^ 1)
theorem ha07212 : a07212.IsHomogeneous 132 := by
  unfold a07212
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07206.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07211.pow 1)))

@[irreducible]
def a07213 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a03865 ^ 1)
theorem ha07213 : a07213.IsHomogeneous 411 := by
  unfold a07213
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07212.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha03865.pow 1)))

@[irreducible]
def a07214 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06742 ^ 1)
theorem ha07214 : a07214.IsHomogeneous 666 := by
  unfold a07214
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06742.pow 1)))

@[irreducible]
def a07215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07214 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06743 ^ 1)
theorem ha07215 : a07215.IsHomogeneous 921 := by
  unfold a07215
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06743.pow 1)))

@[irreducible]
def a07216 : Poly := (C ((-5 : ℂ) / (1152 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06744 ^ 1)
theorem ha07216 : a07216.IsHomogeneous 1175 := by
  unfold a07216
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1152 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06744.pow 1)))

@[irreducible]
def a07217 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07216 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07196 ^ 1)
theorem ha07217 : a07217.IsHomogeneous 1429 := by
  unfold a07217
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07216.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07196.pow 1)))

@[irreducible]
def a07218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a03869 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a07217 ^ 1)
theorem ha07218 : a07218.IsHomogeneous 1508 := by
  unfold a07218
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha03869.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha07217.pow 1)))

@[irreducible]
def a07219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05720 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a07218 ^ 1)
theorem ha07219 : a07219.IsHomogeneous 1587 := by
  unfold a07219
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05720.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha07218.pow 1)))

@[irreducible]
def a07220 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a07219 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05721 ^ 1)
theorem ha07220 : a07220.IsHomogeneous 1666 := by
  unfold a07220
  exact ((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha07219.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05721.pow 1)))

@[irreducible]
def a07221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05722 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a07220 ^ 1)
theorem ha07221 : a07221.IsHomogeneous 1745 := by
  unfold a07221
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05722.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha07220.pow 1)))

@[irreducible]
def a07222 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a07221 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a06738 ^ 1)
theorem ha07222 : a07222.IsHomogeneous 1824 := by
  unfold a07222
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha07221.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha06738.pow 1)))

@[irreducible]
def a07223 : Poly := (C ((-5 : ℂ) / (24 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a07222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a03873 ^ 1)
theorem ha07223 : a07223.IsHomogeneous 1932 := by
  unfold a07223
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (24 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07222.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha03873.pow 1)))

@[irreducible]
def a07224 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a07223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05712 ^ 1)
theorem ha07224 : a07224.IsHomogeneous 2022 := by
  unfold a07224
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha07223.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05712.pow 1)))

@[irreducible]
def a07225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05713 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07224 ^ 1)
theorem ha07225 : a07225.IsHomogeneous 2082 := by
  unfold a07225
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05713.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07224.pow 1)))

@[irreducible]
def a07226 : Poly := (C ((-16 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05716 ^ 1)
theorem ha07226 : a07226.IsHomogeneous 2142 := by
  unfold a07226
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07225.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05716.pow 1)))

@[irreducible]
def a07227 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00834 ^ 1 * a01926 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00825 ^ 1 * a01946 ^ 1)
theorem ha07227 : a07227.IsHomogeneous 348 := by
  unfold a07227
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00834.pow 1)).mul (ha01926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00825.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a07228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a01926 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a03937 ^ 1)
theorem ha07228 : a07228.IsHomogeneous 288 := by
  unfold a07228
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha01926.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha03937.pow 1)))

@[irreducible]
def a07229 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07227 ^ 1)
theorem ha07229 : a07229.IsHomogeneous 348 := by
  unfold a07229
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07228.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07227.pow 1)))

@[irreducible]
def a07230 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00825 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00304 ^ 1 * a03974 ^ 1)
theorem ha07230 : a07230.IsHomogeneous 408 := by
  unfold a07230
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00825.pow 1)).mul (ha01946.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00304.pow 1)).mul (ha03974.pow 1)))

@[irreducible]
def a07231 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07230 ^ 1)
theorem ha07231 : a07231.IsHomogeneous 408 := by
  unfold a07231
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07230.pow 1)))

@[irreducible]
def a07232 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07229 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07231 ^ 1)
theorem ha07232 : a07232.IsHomogeneous 408 := by
  unfold a07232
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07229.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07231.pow 1)))

@[irreducible]
def a07233 : Poly := (C ((-108 : ℂ) / (25 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a01923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00823 ^ 1 * a01896 ^ 1)
theorem ha07233 : a07233.IsHomogeneous 153 := by
  unfold a07233
  exact (((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (25 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha01923.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00823.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a07234 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a00303 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a01896 ^ 1)
theorem ha07234 : a07234.IsHomogeneous 147 := by
  unfold a07234
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a07235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07233 ^ 1)
theorem ha07235 : a07235.IsHomogeneous 153 := by
  unfold a07235
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07233.pow 1)))

@[irreducible]
def a07236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a03933 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a01923 ^ 1)
theorem ha07236 : a07236.IsHomogeneous 159 := by
  unfold a07236
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha03933.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a07237 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a07233 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07236 ^ 1)
theorem ha07237 : a07237.IsHomogeneous 159 := by
  unfold a07237
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha07233.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07236.pow 1)))

@[irreducible]
def a07238 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a07235 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07237 ^ 1)
theorem ha07238 : a07238.IsHomogeneous 159 := by
  unfold a07238
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha07235.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07237.pow 1)))

@[irreducible]
def a07239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02008 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00865 ^ 1)
theorem ha07239 : a07239.IsHomogeneous 24 := by
  unfold a07239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00865.pow 1)))

@[irreducible]
def a07240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07239 ^ 1) + (C ((35 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a03317 ^ 1)
theorem ha07240 : a07240.IsHomogeneous 24 := by
  unfold a07240
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07239.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha03317.pow 1)))

@[irreducible]
def a07241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07240 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a03318 ^ 1)
theorem ha07241 : a07241.IsHomogeneous 24 := by
  unfold a07241
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha03318.pow 1)))

@[irreducible]
def a07242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03319 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a07241 ^ 1)
theorem ha07242 : a07242.IsHomogeneous 24 := by
  unfold a07242
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha07241.pow 1)))

@[irreducible]
def a07243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a04086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02008 ^ 1)
theorem ha07243 : a07243.IsHomogeneous 24 := by
  unfold a07243
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07239 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07243 ^ 1)
theorem ha07244 : a07244.IsHomogeneous 24 := by
  unfold a07244
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07239.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07243.pow 1)))

@[irreducible]
def a07245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07244 ^ 1)
theorem ha07245 : a07245.IsHomogeneous 24 := by
  unfold a07245
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07240.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07244.pow 1)))

@[irreducible]
def a07246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07245 ^ 1)
theorem ha07246 : a07246.IsHomogeneous 24 := by
  unfold a07246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07245.pow 1)))

@[irreducible]
def a07247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07242 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a07246 ^ 1)
theorem ha07247 : a07247.IsHomogeneous 24 := by
  unfold a07247
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha07246.pow 1)))

@[irreducible]
def a07248 : Poly := (C ((-14 : ℂ) / (45 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a06508 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07247 ^ 1)
theorem ha07248 : a07248.IsHomogeneous 24 := by
  unfold a07248
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (45 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha06508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07247.pow 1)))

@[irreducible]
def a07249 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a07248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a03890 ^ 1)
theorem ha07249 : a07249.IsHomogeneous 141 := by
  unfold a07249
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07250 : Poly := (C ((-7 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a07249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07234 ^ 1)
theorem ha07250 : a07250.IsHomogeneous 147 := by
  unfold a07250
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha07249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07234.pow 1)))

@[irreducible]
def a07251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07235 ^ 1)
theorem ha07251 : a07251.IsHomogeneous 153 := by
  unfold a07251
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07235.pow 1)))

@[irreducible]
def a07252 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a07251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07238 ^ 1)
theorem ha07252 : a07252.IsHomogeneous 159 := by
  unfold a07252
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha07251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07238.pow 1)))

@[irreducible]
def a07253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00821 ^ 1 * a01841 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00155 ^ 1 * a01920 ^ 1)
theorem ha07253 : a07253.IsHomogeneous 132 := by
  unfold a07253
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00821.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00155.pow 1)).mul (ha01920.pow 1)))

@[irreducible]
def a07254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00302 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00821 ^ 1 * a01841 ^ 1)
theorem ha07254 : a07254.IsHomogeneous 132 := by
  unfold a07254
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00302.pow 1)).mul (ha03803.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00821.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a07255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07253 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a07254 ^ 1)
theorem ha07255 : a07255.IsHomogeneous 132 := by
  unfold a07255
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha07254.pow 1)))

@[irreducible]
def a07256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03929 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01920 ^ 1)
theorem ha07256 : a07256.IsHomogeneous 129 := by
  unfold a07256
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01920.pow 1)))

@[irreducible]
def a07257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07253 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07256 ^ 1)
theorem ha07257 : a07257.IsHomogeneous 132 := by
  unfold a07257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07256.pow 1)))

@[irreducible]
def a07258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07257 ^ 1)
theorem ha07258 : a07258.IsHomogeneous 132 := by
  unfold a07258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07257.pow 1)))

@[irreducible]
def a07259 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00302 ^ 1 * a03803 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a07120 ^ 1)
theorem ha07259 : a07259.IsHomogeneous 132 := by
  unfold a07259
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00302.pow 1)).mul (ha03803.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07120.pow 1)))

@[irreducible]
def a07260 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a07259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07254 ^ 1)
theorem ha07260 : a07260.IsHomogeneous 132 := by
  unfold a07260
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha07259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07254.pow 1)))

@[irreducible]
def a07261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07255 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a07260 ^ 1)
theorem ha07261 : a07261.IsHomogeneous 132 := by
  unfold a07261
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha07260.pow 1)))

@[irreducible]
def a07262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07261 ^ 1)
theorem ha07262 : a07262.IsHomogeneous 132 := by
  unfold a07262
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07261.pow 1)))

@[irreducible]
def a07263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00812 ^ 1 * a01917 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a01903 ^ 1)
theorem ha07263 : a07263.IsHomogeneous 123 := by
  unfold a07263
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00812.pow 1)).mul (ha01917.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a07264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00301 ^ 1 * a03811 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a01903 ^ 1)
theorem ha07264 : a07264.IsHomogeneous 117 := by
  unfold a07264
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a07265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07264 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a07263 ^ 1)
theorem ha07265 : a07265.IsHomogeneous 123 := by
  unfold a07265
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07264.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha07263.pow 1)))

@[irreducible]
def a07266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a03925 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01917 ^ 1)
theorem ha07266 : a07266.IsHomogeneous 120 := by
  unfold a07266
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha03925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a07267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07263 ^ 1)
theorem ha07267 : a07267.IsHomogeneous 123 := by
  unfold a07267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07263.pow 1)))

@[irreducible]
def a07268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07265 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a07267 ^ 1)
theorem ha07268 : a07268.IsHomogeneous 123 := by
  unfold a07268
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha07267.pow 1)))

@[irreducible]
def a07269 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a07132 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a03811 ^ 1)
theorem ha07269 : a07269.IsHomogeneous 102 := by
  unfold a07269
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha07132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a07270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a07269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07264 ^ 1)
theorem ha07270 : a07270.IsHomogeneous 117 := by
  unfold a07270
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha07269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07264.pow 1)))

@[irreducible]
def a07271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07265 ^ 1)
theorem ha07271 : a07271.IsHomogeneous 123 := by
  unfold a07271
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07265.pow 1)))

@[irreducible]
def a07272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07271 ^ 1)
theorem ha07272 : a07272.IsHomogeneous 123 := by
  unfold a07272
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07271.pow 1)))

@[irreducible]
def a07273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00712 ^ 1 * a01914 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00817 ^ 1 * a01702 ^ 1)
theorem ha07273 : a07273.IsHomogeneous 102 := by
  unfold a07273
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha01914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00817.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a07274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00817 ^ 1 * a01702 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00300 ^ 1 * a03562 ^ 1)
theorem ha07274 : a07274.IsHomogeneous 105 := by
  unfold a07274
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00817.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00300.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07273 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a07274 ^ 1)
theorem ha07275 : a07275.IsHomogeneous 105 := by
  unfold a07275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha07274.pow 1)))

@[irreducible]
def a07276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01914 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a03921 ^ 1)
theorem ha07276 : a07276.IsHomogeneous 99 := by
  unfold a07276
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01914.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha03921.pow 1)))

@[irreducible]
def a07277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07276 ^ 1)
theorem ha07277 : a07277.IsHomogeneous 105 := by
  unfold a07277
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07273.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07276.pow 1)))

@[irreducible]
def a07278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07277 ^ 1)
theorem ha07278 : a07278.IsHomogeneous 105 := by
  unfold a07278
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07275.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07277.pow 1)))

@[irreducible]
def a07279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00126 ^ 1 * a06725 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00300 ^ 1 * a03562 ^ 1)
theorem ha07279 : a07279.IsHomogeneous 105 := by
  unfold a07279
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00300.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07274 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a07279 ^ 1)
theorem ha07280 : a07280.IsHomogeneous 105 := by
  unfold a07280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07274.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha07279.pow 1)))

@[irreducible]
def a07281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07275 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a07280 ^ 1)
theorem ha07281 : a07281.IsHomogeneous 105 := by
  unfold a07281
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07275.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha07280.pow 1)))

@[irreducible]
def a07282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07281 ^ 1)
theorem ha07282 : a07282.IsHomogeneous 105 := by
  unfold a07282
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07281.pow 1)))

@[irreducible]
def a07283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01896 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00809 ^ 1 * a00865 ^ 1)
theorem ha07283 : a07283.IsHomogeneous 48 := by
  unfold a07283
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00809.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a00865 ^ 1)
theorem ha07284 : a07284.IsHomogeneous 48 := by
  unfold a07284
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07283 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a07284 ^ 1)
theorem ha07285 : a07285.IsHomogeneous 48 := by
  unfold a07285
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha07284.pow 1)))

@[irreducible]
def a07286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a03890 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a00317 ^ 1 * a01896 ^ 1)
theorem ha07286 : a07286.IsHomogeneous 48 := by
  unfold a07286
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha00317.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a07287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07283 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a07286 ^ 1)
theorem ha07287 : a07287.IsHomogeneous 48 := by
  unfold a07287
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha07286.pow 1)))

@[irreducible]
def a07288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07287 ^ 1)
theorem ha07288 : a07288.IsHomogeneous 48 := by
  unfold a07288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07287.pow 1)))

@[irreducible]
def a07289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04086 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02008 ^ 1)
theorem ha07289 : a07289.IsHomogeneous 48 := by
  unfold a07289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07284 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a07289 ^ 1)
theorem ha07290 : a07290.IsHomogeneous 48 := by
  unfold a07290
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07284.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha07289.pow 1)))

@[irreducible]
def a07291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07285 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a07290 ^ 1)
theorem ha07291 : a07291.IsHomogeneous 48 := by
  unfold a07291
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha07290.pow 1)))

@[irreducible]
def a07292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07288 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07291 ^ 1)
theorem ha07292 : a07292.IsHomogeneous 48 := by
  unfold a07292
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07291.pow 1)))

@[irreducible]
def a07293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a07248 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a03890 ^ 1)
theorem ha07293 : a07293.IsHomogeneous 48 := by
  unfold a07293
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07286 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07293 ^ 1)
theorem ha07294 : a07294.IsHomogeneous 48 := by
  unfold a07294
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07293.pow 1)))

@[irreducible]
def a07295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07287 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a07294 ^ 1)
theorem ha07295 : a07295.IsHomogeneous 48 := by
  unfold a07295
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07287.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha07294.pow 1)))

@[irreducible]
def a07296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07288 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07295 ^ 1)
theorem ha07296 : a07296.IsHomogeneous 48 := by
  unfold a07296
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07295.pow 1)))

@[irreducible]
def a07297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07296 ^ 1)
theorem ha07297 : a07297.IsHomogeneous 48 := by
  unfold a07297
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07296.pow 1)))

@[irreducible]
def a07298 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a03921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07297 ^ 1)
theorem ha07298 : a07298.IsHomogeneous 93 := by
  unfold a07298
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha03921.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07297.pow 1)))

@[irreducible]
def a07299 : Poly := (C ((-5 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a07298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07276 ^ 1)
theorem ha07299 : a07299.IsHomogeneous 99 := by
  unfold a07299
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha07298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07276.pow 1)))

@[irreducible]
def a07300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07277 ^ 1)
theorem ha07300 : a07300.IsHomogeneous 105 := by
  unfold a07300
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07299.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07277.pow 1)))

@[irreducible]
def a07301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07300 ^ 1)
theorem ha07301 : a07301.IsHomogeneous 105 := by
  unfold a07301
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07300.pow 1)))

@[irreducible]
def a07302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07301 ^ 1)
theorem ha07302 : a07302.IsHomogeneous 105 := by
  unfold a07302
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07301.pow 1)))

@[irreducible]
def a07303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a03925 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00127 ^ 1 * a07302 ^ 1)
theorem ha07303 : a07303.IsHomogeneous 123 := by
  unfold a07303
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha03925.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00127.pow 1)).mul (ha07302.pow 1)))

@[irreducible]
def a07304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07303 ^ 1)
theorem ha07304 : a07304.IsHomogeneous 123 := by
  unfold a07304
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07303.pow 1)))

@[irreducible]
def a07305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07304 ^ 1)
theorem ha07305 : a07305.IsHomogeneous 123 := by
  unfold a07305
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07304.pow 1)))

@[irreducible]
def a07306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07268 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a07305 ^ 1)
theorem ha07306 : a07306.IsHomogeneous 123 := by
  unfold a07306
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha07305.pow 1)))

@[irreducible]
def a07307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07306 ^ 1)
theorem ha07307 : a07307.IsHomogeneous 123 := by
  unfold a07307
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07306.pow 1)))

@[irreducible]
def a07308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03929 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a07307 ^ 1)
theorem ha07308 : a07308.IsHomogeneous 129 := by
  unfold a07308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha07307.pow 1)))

@[irreducible]
def a07309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07308 ^ 1)
theorem ha07309 : a07309.IsHomogeneous 135 := by
  unfold a07309
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07256.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07308.pow 1)))

@[irreducible]
def a07310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07257 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a07309 ^ 1)
theorem ha07310 : a07310.IsHomogeneous 135 := by
  unfold a07310
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha07309.pow 1)))

@[irreducible]
def a07311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07310 ^ 1)
theorem ha07311 : a07311.IsHomogeneous 135 := by
  unfold a07311
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07258.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07310.pow 1)))

@[irreducible]
def a07312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07311 ^ 1)
theorem ha07312 : a07312.IsHomogeneous 135 := by
  unfold a07312
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07311.pow 1)))

@[irreducible]
def a07313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07312 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a03933 ^ 1)
theorem ha07313 : a07313.IsHomogeneous 165 := by
  unfold a07313
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07312.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha03933.pow 1)))

@[irreducible]
def a07314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07313 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07236 ^ 1)
theorem ha07314 : a07314.IsHomogeneous 165 := by
  unfold a07314
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07236.pow 1)))

@[irreducible]
def a07315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07314 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07237 ^ 1)
theorem ha07315 : a07315.IsHomogeneous 165 := by
  unfold a07315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07314.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07237.pow 1)))

@[irreducible]
def a07316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07315 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07238 ^ 1)
theorem ha07316 : a07316.IsHomogeneous 165 := by
  unfold a07316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07315.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07238.pow 1)))

@[irreducible]
def a07317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07316 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07252 ^ 1)
theorem ha07317 : a07317.IsHomogeneous 165 := by
  unfold a07317
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07252.pow 1)))

@[irreducible]
def a07318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a03937 ^ 1) + (C ((4 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07317 ^ 1)
theorem ha07318 : a07318.IsHomogeneous 225 := by
  unfold a07318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha03937.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07317.pow 1)))

@[irreducible]
def a07319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07228 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a07318 ^ 1)
theorem ha07319 : a07319.IsHomogeneous 288 := by
  unfold a07319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07228.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07318.pow 1)))

@[irreducible]
def a07320 : Poly := (C ((-2 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07229 ^ 1)
theorem ha07320 : a07320.IsHomogeneous 348 := by
  unfold a07320
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07229.pow 1)))

@[irreducible]
def a07321 : Poly := (C ((-5 : ℂ) / (108 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07320 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07232 ^ 1)
theorem ha07321 : a07321.IsHomogeneous 408 := by
  unfold a07321
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (108 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07320.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07232.pow 1)))

@[irreducible]
def a07322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a03945 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a01929 ^ 1 * a01944 ^ 1)
theorem ha07322 : a07322.IsHomogeneous 306 := by
  unfold a07322
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha03945.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha01929.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a07323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01929 ^ 1 * a01944 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a03971 ^ 1)
theorem ha07323 : a07323.IsHomogeneous 282 := by
  unfold a07323
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01929.pow 1)).mul (ha01944.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a07324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07322 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a07323 ^ 1)
theorem ha07324 : a07324.IsHomogeneous 306 := by
  unfold a07324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07322.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha07323.pow 1)))

@[irreducible]
def a07325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a03943 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a00305 ^ 1 * a01944 ^ 1)
theorem ha07325 : a07325.IsHomogeneous 240 := by
  unfold a07325
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha03943.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha00305.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a07326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01944 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a03971 ^ 1)
theorem ha07326 : a07326.IsHomogeneous 216 := by
  unfold a07326
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01944.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a07327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07325 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a07326 ^ 1)
theorem ha07327 : a07327.IsHomogeneous 240 := by
  unfold a07327
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07325.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha07326.pow 1)))

@[irreducible]
def a07328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a01944 ^ 1)
theorem ha07328 : a07328.IsHomogeneous 174 := by
  unfold a07328
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a07329 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 2)
theorem ha07329 : a07329.IsHomogeneous 132 := by
  unfold a07329
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 2)))

@[irreducible]
def a07330 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07329 ^ 1)
theorem ha07330 : a07330.IsHomogeneous 132 := by
  unfold a07330
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07329.pow 1)))

@[irreducible]
def a07331 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a07330 ^ 1)
theorem ha07331 : a07331.IsHomogeneous 198 := by
  unfold a07331
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07328.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha07330.pow 1)))

@[irreducible]
def a07332 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a03943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a07331 ^ 1)
theorem ha07332 : a07332.IsHomogeneous 264 := by
  unfold a07332
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha03943.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha07331.pow 1)))

@[irreducible]
def a07333 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07325 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07332 ^ 1)
theorem ha07333 : a07333.IsHomogeneous 264 := by
  unfold a07333
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07332.pow 1)))

@[irreducible]
def a07334 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07333 ^ 1)
theorem ha07334 : a07334.IsHomogeneous 264 := by
  unfold a07334
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07333.pow 1)))

@[irreducible]
def a07335 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a03945 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a07334 ^ 1)
theorem ha07335 : a07335.IsHomogeneous 330 := by
  unfold a07335
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha03945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha07334.pow 1)))

@[irreducible]
def a07336 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07322 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07335 ^ 1)
theorem ha07336 : a07336.IsHomogeneous 330 := by
  unfold a07336
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07322.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07335.pow 1)))

@[irreducible]
def a07337 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07336 ^ 1)
theorem ha07337 : a07337.IsHomogeneous 330 := by
  unfold a07337
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07336.pow 1)))

@[irreducible]
def a07338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01941 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00831 ^ 1 * a00865 ^ 1)
theorem ha07338 : a07338.IsHomogeneous 147 := by
  unfold a07338
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01941.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00831.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07339 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1 * a00865 ^ 1)
theorem ha07339 : a07339.IsHomogeneous 105 := by
  unfold a07339
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a07340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07338 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07339 ^ 1)
theorem ha07340 : a07340.IsHomogeneous 147 := by
  unfold a07340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07338.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07339.pow 1)))

@[irreducible]
def a07341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a03967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01941 ^ 1)
theorem ha07341 : a07341.IsHomogeneous 153 := by
  unfold a07341
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha03967.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a07342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07338 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07341 ^ 1)
theorem ha07342 : a07342.IsHomogeneous 153 := by
  unfold a07342
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07338.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07341.pow 1)))

@[irreducible]
def a07343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07342 ^ 1)
theorem ha07343 : a07343.IsHomogeneous 153 := by
  unfold a07343
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07342.pow 1)))

@[irreducible]
def a07344 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02008 ^ 1)
theorem ha07344 : a07344.IsHomogeneous 60 := by
  unfold a07344
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a07345 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a07344 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07339 ^ 1)
theorem ha07345 : a07345.IsHomogeneous 105 := by
  unfold a07345
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07344.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07339.pow 1)))

@[irreducible]
def a07346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07340 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07345 ^ 1)
theorem ha07346 : a07346.IsHomogeneous 147 := by
  unfold a07346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07340.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07345.pow 1)))

@[irreducible]
def a07347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07343 ^ 1)
theorem ha07347 : a07347.IsHomogeneous 153 := by
  unfold a07347
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07346.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07343.pow 1)))

@[irreducible]
def a07348 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a01702 ^ 1)
theorem ha07348 : a07348.IsHomogeneous 135 := by
  unfold a07348
  exact (((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a07349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a03562 ^ 1)
theorem ha07349 : a07349.IsHomogeneous 135 := by
  unfold a07349
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha01702.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07349 ^ 1)
theorem ha07350 : a07350.IsHomogeneous 135 := by
  unfold a07350
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07349.pow 1)))

@[irreducible]
def a07351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03963 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01938 ^ 1)
theorem ha07351 : a07351.IsHomogeneous 135 := by
  unfold a07351
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03963.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a07352 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07351 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07348 ^ 1)
theorem ha07352 : a07352.IsHomogeneous 135 := by
  unfold a07352
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07351.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07348.pow 1)))

@[irreducible]
def a07353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07352 ^ 1)
theorem ha07353 : a07353.IsHomogeneous 135 := by
  unfold a07353
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07352.pow 1)))

@[irreducible]
def a07354 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a06725 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03562 ^ 1)
theorem ha07354 : a07354.IsHomogeneous 93 := by
  unfold a07354
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07349 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07354 ^ 1)
theorem ha07355 : a07355.IsHomogeneous 135 := by
  unfold a07355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07349.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07354.pow 1)))

@[irreducible]
def a07356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07355 ^ 1)
theorem ha07356 : a07356.IsHomogeneous 135 := by
  unfold a07356
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07355.pow 1)))

@[irreducible]
def a07357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07356 ^ 1)
theorem ha07357 : a07357.IsHomogeneous 135 := by
  unfold a07357
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07356.pow 1)))

@[irreducible]
def a07358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01702 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a03562 ^ 1)
theorem ha07358 : a07358.IsHomogeneous 99 := by
  unfold a07358
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a07359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07358 ^ 1)
theorem ha07359 : a07359.IsHomogeneous 99 := by
  unfold a07359
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01702.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07358.pow 1)))

@[irreducible]
def a07360 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00260 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a06725 ^ 1)
theorem ha07360 : a07360.IsHomogeneous 93 := by
  unfold a07360
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00260.pow 1)).mul (ha03562.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a07361 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a07360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07358 ^ 1)
theorem ha07361 : a07361.IsHomogeneous 99 := by
  unfold a07361
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha07360.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07358.pow 1)))

@[irreducible]
def a07362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07359 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07361 ^ 1)
theorem ha07362 : a07362.IsHomogeneous 99 := by
  unfold a07362
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07361.pow 1)))

@[irreducible]
def a07363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07359 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07362 ^ 1)
theorem ha07363 : a07363.IsHomogeneous 99 := by
  unfold a07363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07362.pow 1)))

@[irreducible]
def a07364 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a07363 ^ 1)
theorem ha07364 : a07364.IsHomogeneous 135 := by
  unfold a07364
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a07365 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07364 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07351 ^ 1)
theorem ha07365 : a07365.IsHomogeneous 135 := by
  unfold a07365
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07364.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07351.pow 1)))

@[irreducible]
def a07366 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07365 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07352 ^ 1)
theorem ha07366 : a07366.IsHomogeneous 135 := by
  unfold a07366
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07365.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07352.pow 1)))

@[irreducible]
def a07367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07366 ^ 1)
theorem ha07367 : a07367.IsHomogeneous 135 := by
  unfold a07367
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07366.pow 1)))

@[irreducible]
def a07368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07357 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07367 ^ 1)
theorem ha07368 : a07368.IsHomogeneous 135 := by
  unfold a07368
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07357.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07367.pow 1)))

@[irreducible]
def a07369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a03967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a07368 ^ 1)
theorem ha07369 : a07369.IsHomogeneous 159 := by
  unfold a07369
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha03967.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha07368.pow 1)))

@[irreducible]
def a07370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07369 ^ 1)
theorem ha07370 : a07370.IsHomogeneous 159 := by
  unfold a07370
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07341.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07369.pow 1)))

@[irreducible]
def a07371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07370 ^ 1)
theorem ha07371 : a07371.IsHomogeneous 159 := by
  unfold a07371
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07342.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07370.pow 1)))

@[irreducible]
def a07372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07343 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07371 ^ 1)
theorem ha07372 : a07372.IsHomogeneous 159 := by
  unfold a07372
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07343.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07371.pow 1)))

@[irreducible]
def a07373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07372 ^ 1)
theorem ha07373 : a07373.IsHomogeneous 159 := by
  unfold a07373
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07372.pow 1)))

@[irreducible]
def a07374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a03971 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07373 ^ 1)
theorem ha07374 : a07374.IsHomogeneous 219 := by
  unfold a07374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha03971.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07373.pow 1)))

@[irreducible]
def a07375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07323 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a07374 ^ 1)
theorem ha07375 : a07375.IsHomogeneous 282 := by
  unfold a07375
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07323.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07374.pow 1)))

@[irreducible]
def a07376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07324 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00042 ^ 1 * a07375 ^ 1)
theorem ha07376 : a07376.IsHomogeneous 306 := by
  unfold a07376
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00042.pow 1)).mul (ha07375.pow 1)))

@[irreducible]
def a07377 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a07376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07337 ^ 1)
theorem ha07377 : a07377.IsHomogeneous 330 := by
  unfold a07377
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha07376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07337.pow 1)))

@[irreducible]
def a07378 : Poly := (C ((-15 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a07377 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1 * a03974 ^ 1)
theorem ha07378 : a07378.IsHomogeneous 378 := by
  unfold a07378
  exact (((((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07377.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)).mul (ha03974.pow 1)))

@[irreducible]
def a07379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07378 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07230 ^ 1)
theorem ha07379 : a07379.IsHomogeneous 408 := by
  unfold a07379
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07378.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07230.pow 1)))

@[irreducible]
def a07380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07379 ^ 1)
theorem ha07380 : a07380.IsHomogeneous 408 := by
  unfold a07380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07379.pow 1)))

@[irreducible]
def a07381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07380 ^ 1)
theorem ha07381 : a07381.IsHomogeneous 408 := by
  unfold a07381
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07380.pow 1)))

@[irreducible]
def a07382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07381 ^ 1)
theorem ha07382 : a07382.IsHomogeneous 408 := by
  unfold a07382
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07381.pow 1)))

@[irreducible]
def a07383 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a03978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a07382 ^ 1)
theorem ha07383 : a07383.IsHomogeneous 834 := by
  unfold a07383
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha03978.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha07382.pow 1)))

@[irreducible]
def a07384 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a05714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07383 ^ 1)
theorem ha07384 : a07384.IsHomogeneous 1167 := by
  unfold a07384
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha05714.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07383.pow 1)))

@[irreducible]
def a07385 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a05715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07384 ^ 1)
theorem ha07385 : a07385.IsHomogeneous 1500 := by
  unfold a07385
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha05715.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07384.pow 1)))

@[irreducible]
def a07386 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a05716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07385 ^ 1)
theorem ha07386 : a07386.IsHomogeneous 1833 := by
  unfold a07386
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha05716.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07385.pow 1)))

@[irreducible]
def a07387 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a07226 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07386 ^ 1)
theorem ha07387 : a07387.IsHomogeneous 2166 := by
  unfold a07387
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha07226.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07386.pow 1)))

@[irreducible]
def a07388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01979 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a01886 ^ 1)
theorem ha07388 : a07388.IsHomogeneous 1344 := by
  unfold a07388
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01979.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a07389 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a01886 ^ 1)
theorem ha07389 : a07389.IsHomogeneous 1641 := by
  unfold a07389
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a07390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07388 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a07389 ^ 1)
theorem ha07390 : a07390.IsHomogeneous 1677 := by
  unfold a07390
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07388.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha07389.pow 1)))

@[irreducible]
def a07391 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a04032 ^ 1)
theorem ha07391 : a07391.IsHomogeneous 1047 := by
  unfold a07391
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01979.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a07392 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a07388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07391 ^ 1)
theorem ha07392 : a07392.IsHomogeneous 1380 := by
  unfold a07392
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha07388.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07391.pow 1)))

@[irreducible]
def a07393 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a07390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07392 ^ 1)
theorem ha07393 : a07393.IsHomogeneous 1713 := by
  unfold a07393
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha07390.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07392.pow 1)))

@[irreducible]
def a07394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a03873 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a07222 ^ 1)
theorem ha07394 : a07394.IsHomogeneous 1908 := by
  unfold a07394
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha03873.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a07395 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a07394 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07389 ^ 1)
theorem ha07395 : a07395.IsHomogeneous 1974 := by
  unfold a07395
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha07394.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07389.pow 1)))

@[irreducible]
def a07396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07390 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00100 ^ 1 * a07395 ^ 1)
theorem ha07396 : a07396.IsHomogeneous 2010 := by
  unfold a07396
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07390.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00100.pow 1)).mul (ha07395.pow 1)))

@[irreducible]
def a07397 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a07396 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07393 ^ 1)
theorem ha07397 : a07397.IsHomogeneous 2046 := by
  unfold a07397
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha07396.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07393.pow 1)))

@[irreducible]
def a07398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00846 ^ 1 * a01976 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00848 ^ 1 * a01970 ^ 1)
theorem ha07398 : a07398.IsHomogeneous 216 := by
  unfold a07398
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00846.pow 1)).mul (ha01976.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00848.pow 1)).mul (ha01970.pow 1)))

@[irreducible]
def a07399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a01970 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a04015 ^ 1)
theorem ha07399 : a07399.IsHomogeneous 177 := by
  unfold a07399
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha01970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04015.pow 1)))

@[irreducible]
def a07400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07398 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a07399 ^ 1)
theorem ha07400 : a07400.IsHomogeneous 216 := by
  unfold a07400
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07398.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha07399.pow 1)))

@[irreducible]
def a07401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00309 ^ 1 * a04028 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a00846 ^ 1 * a01976 ^ 1)
theorem ha07401 : a07401.IsHomogeneous 252 := by
  unfold a07401
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00309.pow 1)).mul (ha04028.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha00846.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a07402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07401 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a07398 ^ 1)
theorem ha07402 : a07402.IsHomogeneous 252 := by
  unfold a07402
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07401.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha07398.pow 1)))

@[irreducible]
def a07403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07402 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00100 ^ 1 * a07400 ^ 1)
theorem ha07403 : a07403.IsHomogeneous 252 := by
  unfold a07403
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07402.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00100.pow 1)).mul (ha07400.pow 1)))

@[irreducible]
def a07404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00843 ^ 1 * a01841 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a01965 ^ 1)
theorem ha07404 : a07404.IsHomogeneous 90 := by
  unfold a07404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00843.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01965.pow 1)))

@[irreducible]
def a07405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00308 ^ 1 * a03803 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00843 ^ 1 * a01841 ^ 1)
theorem ha07405 : a07405.IsHomogeneous 96 := by
  unfold a07405
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00308.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00843.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a07406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07405 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07404 ^ 1)
theorem ha07406 : a07406.IsHomogeneous 96 := by
  unfold a07406
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07405.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07404.pow 1)))

@[irreducible]
def a07407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01965 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04008 ^ 1)
theorem ha07407 : a07407.IsHomogeneous 81 := by
  unfold a07407
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01965.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04008.pow 1)))

@[irreducible]
def a07408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07404 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a07407 ^ 1)
theorem ha07408 : a07408.IsHomogeneous 90 := by
  unfold a07408
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07404.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha07407.pow 1)))

@[irreducible]
def a07409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07406 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07408 ^ 1)
theorem ha07409 : a07409.IsHomogeneous 96 := by
  unfold a07409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07406.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07408.pow 1)))

@[irreducible]
def a07410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00812 ^ 1 * a01962 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00841 ^ 1 * a01903 ^ 1)
theorem ha07410 : a07410.IsHomogeneous 75 := by
  unfold a07410
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00812.pow 1)).mul (ha01962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00841.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a07411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a00298 ^ 1 * a03811 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a01903 ^ 1)
theorem ha07411 : a07411.IsHomogeneous 75 := by
  unfold a07411
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a07412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07410 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a07411 ^ 1)
theorem ha07412 : a07412.IsHomogeneous 75 := by
  unfold a07412
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07410.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha07411.pow 1)))

@[irreducible]
def a07413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a04004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01962 ^ 1)
theorem ha07413 : a07413.IsHomogeneous 72 := by
  unfold a07413
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha04004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a07414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07413 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07410 ^ 1)
theorem ha07414 : a07414.IsHomogeneous 75 := by
  unfold a07414
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07413.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07410.pow 1)))

@[irreducible]
def a07415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07414 ^ 1)
theorem ha07415 : a07415.IsHomogeneous 75 := by
  unfold a07415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07414.pow 1)))

@[irreducible]
def a07416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00126 ^ 1 * a07132 ^ 1)
theorem ha07416 : a07416.IsHomogeneous 36 := by
  unfold a07416
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00126.pow 1)).mul (ha07132.pow 1)))

@[irreducible]
def a07417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a07416 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07411 ^ 1)
theorem ha07417 : a07417.IsHomogeneous 75 := by
  unfold a07417
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha07416.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07411.pow 1)))

@[irreducible]
def a07418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07412 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a07417 ^ 1)
theorem ha07418 : a07418.IsHomogeneous 75 := by
  unfold a07418
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha07417.pow 1)))

@[irreducible]
def a07419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07415 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07418 ^ 1)
theorem ha07419 : a07419.IsHomogeneous 75 := by
  unfold a07419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07418.pow 1)))

@[irreducible]
def a07420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00298 ^ 1 * a03890 ^ 1)
theorem ha07420 : a07420.IsHomogeneous 57 := by
  unfold a07420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00298.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00809 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07420 ^ 1)
theorem ha07421 : a07421.IsHomogeneous 57 := by
  unfold a07421
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 1)).mul (ha01896.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07420.pow 1)))

@[irreducible]
def a07422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a07248 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a03890 ^ 1)
theorem ha07422 : a07422.IsHomogeneous 57 := by
  unfold a07422
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a07423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07420 ^ 1) + (C ((7 : ℂ) / (324 : ℂ)) * a07422 ^ 1)
theorem ha07423 : a07423.IsHomogeneous 57 := by
  unfold a07423
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (324 : ℂ))).mul (ha07422.pow 1)))

end CycleQ2Concrete
