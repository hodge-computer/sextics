import Proposal.CurrentData
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Basic

/-! Actual denominator specialization at (X1,X2,Y0,Y1,Y2)=(1,1,2,2,1).
Exact rational reductions and Bezout data certify the specialized gcd.
Monicity in X0 transports this result to complex multivariate coprimality
and proves nonvanishing of the concrete denominator. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace CycleQ2Concrete.Denominator
abbrev UPoly := Polynomial ℂ

def specVars : Fin 6 → UPoly := ![Polynomial.X, 1, 1, 2, 2, 1]
def spec : CycleQ2Concrete.Poly →+* UPoly :=
  MvPolynomial.eval₂Hom Polynomial.C specVars

def f : UPoly := Polynomial.X^6 + 2*Polynomial.X^3 + Polynomial.X + 132

@[simp] lemma spec_C (c : ℂ) : spec (MvPolynomial.C c) = Polynomial.C c := by
  simp [spec]
@[simp] lemma spec_X (i : Fin 6) : spec (MvPolynomial.X i) = specVars i := by
  simp [spec]

/-- Explicit polynomial quotient witness, rather than an unproved reduction oracle. -/
def Modulo (p r : UPoly) : Prop := ∃ q, p = f*q+r

lemma Modulo.refl (p : UPoly) : Modulo p p := ⟨0, by ring⟩
lemma Modulo.add {p r p' r' : UPoly} (h : Modulo p r) (h' : Modulo p' r') :
    Modulo (p+p') (r+r') := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨q', hq'⟩ := h'
  refine ⟨q+q', ?_⟩
  rw [hq, hq']
  ring
lemma Modulo.mul {p r p' r' : UPoly} (h : Modulo p r) (h' : Modulo p' r') :
    Modulo (p*p') (r*r') := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨q', hq'⟩ := h'
  refine ⟨f*q*q'+q*r'+q'*r, ?_⟩
  rw [hq, hq']
  ring
lemma Modulo.pow {p r : UPoly} (h : Modulo p r) (n : ℕ) :
    Modulo (p^n) (r^n) := by
  induction n with
  | zero => simpa using Modulo.refl (1 : UPoly)
  | succ n ih => simpa only [pow_succ] using ih.mul h
lemma Modulo.trans {p r s : UPoly} (h : Modulo p r) (h' : Modulo r s) :
    Modulo p s := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨q', hq'⟩ := h'
  refine ⟨q+q', ?_⟩
  rw [hq, hq']
  ring
lemma coprime_of_modulo {p r u v : UPoly} (h : Modulo p r)
    (hb : u*f+v*r=1) : IsCoprime f p := by
  obtain ⟨q, hq⟩ := h
  refine ⟨u-v*q, v, ?_⟩
  rw [hq]
  linear_combination hb
lemma coprime_power {p : UPoly} (h : IsCoprime f p) (n : ℕ) : IsCoprime f (p^n) := by
  induction n with
  | zero =>
      change IsCoprime f 1
      exact ⟨0, 1, by ring⟩
  | succ n ih => simpa only [pow_succ] using ih.mul_right h

/-- Exact binding of the small univariate polynomial to the original sextic. -/
theorem specialized_originalF : spec CycleQ2Workspace.originalF = f := by
  apply Polynomial.funext
  intro x
  unfold CycleQ2Workspace.originalF HodgeSubmission.F f
  simp [map_add, map_mul, map_pow, specVars]
  norm_num <;> ring

def r00000 : UPoly := (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1)
def q00000 : UPoly := 0
lemma mod_a00000 : Modulo (spec a00000) r00000 := by
  refine ⟨q00000, ?_⟩
  norm_num [a00000, spec, specVars, r00000, q00000, Matrix.cons_val, Polynomial.C_ofNat]

def r00001 : UPoly := (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00001 : UPoly := 0
lemma mod_a00001 : Modulo (spec a00001) r00001 := by
  refine ⟨q00001, ?_⟩
  norm_num [a00001, spec, specVars, r00001, q00001, Matrix.cons_val, Polynomial.C_ofNat]

def r00002 : UPoly := (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00002 : UPoly := 0
lemma mod_a00002 : Modulo (spec a00002) r00002 := by
  refine ⟨q00002, ?_⟩
  norm_num [a00002, spec, specVars, r00002, q00002, Polynomial.C_ofNat]
  rfl

def r00003 : UPoly := (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00003 : UPoly := 0
lemma mod_a00003 : Modulo (spec a00003) r00003 := by
  refine ⟨q00003, ?_⟩
  norm_num [a00003, spec, specVars, r00003, q00003, Polynomial.C_ofNat]
  rfl

def r00004 : UPoly := (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00004 : UPoly := 0
lemma mod_a00004 : Modulo (spec a00004) r00004 := by
  refine ⟨q00004, ?_⟩
  norm_num [a00004, spec, specVars, r00004, q00004, Polynomial.C_ofNat]
  rfl

def r00005 : UPoly := (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00005 : UPoly := 0
lemma mod_a00005 : Modulo (spec a00005) r00005 := by
  refine ⟨q00005, ?_⟩
  norm_num [a00005, spec, specVars, r00005, q00005, Polynomial.C_ofNat]
  rfl

def r00006 : UPoly := (Polynomial.C ((65 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00006 : UPoly := 0
lemma mod_a00006 : Modulo (spec a00006) r00006 := by
  have h : Modulo (spec a00006) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00004 ^ 6)) := by
    unfold a00006
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00004.pow 6)))
  apply h.trans
  refine ⟨q00006, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00006, r00006, r00001, r00004, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00007 : UPoly := (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00007 : UPoly := 0
lemma mod_a00007 : Modulo (spec a00007) r00007 := by
  have h : Modulo (spec a00007) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00005 ^ 6)) := by
    unfold a00007
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)))
  apply h.trans
  refine ⟨q00007, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00007, r00007, r00002, r00005, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00008 : UPoly := (Polynomial.C ((68 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00008 : UPoly := 0
lemma mod_a00008 : Modulo (spec a00008) r00008 := by
  have h : Modulo (spec a00008) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00001 ^ 3 * r00002 ^ 1 * r00004 ^ 1 * r00005 ^ 1)) := by
    unfold a00008
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1))).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00001.pow 3)).mul (mod_a00002.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)))
  apply h.trans
  refine ⟨q00008, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00008, r00008, r00001, r00002, r00004, r00005, r00006, r00007, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00009 : UPoly := (Polynomial.C ((-68 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00009 : UPoly := (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a00009 : Modulo (spec a00009) r00009 := by
  have h : Modulo (spec a00009) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 6)) := by
    unfold a00009
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)))
  apply h.trans
  refine ⟨q00009, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00009, r00009, r00000, r00003, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00012 : UPoly := (Polynomial.C ((-63 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00012 : UPoly := 0
lemma mod_a00012 : Modulo (spec a00012) r00012 := by
  have h : Modulo (spec a00012) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00004 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 6)) := by
    unfold a00012
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00004.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 6)))
  apply h.trans
  refine ⟨q00012, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00012, r00012, r00001, r00004, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00013 : UPoly := (Polynomial.C ((-188 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0)
def q00013 : UPoly := 0
lemma mod_a00013 : Modulo (spec a00013) r00013 := by
  have h : Modulo (spec a00013) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00012 ^ 1) + (Polynomial.C ((1 : ℂ) / (6 : ℂ)) * r00001 ^ 3 * r00002 ^ 1 * r00004 ^ 1 * r00005 ^ 1)) := by
    unfold a00013
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (6 : ℂ)))).mul (mod_a00001.pow 3)).mul (mod_a00002.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)))
  apply h.trans
  refine ⟨q00013, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00013, r00013, r00001, r00002, r00004, r00005, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00014 : UPoly := (Polynomial.C ((196 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00014 : UPoly := (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a00014 : Modulo (spec a00014) r00014 := by
  have h : Modulo (spec a00014) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00000 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 6)) := by
    unfold a00014
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)))
  apply h.trans
  refine ⟨q00014, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00014, r00014, r00000, r00003, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00015 : UPoly := (Polynomial.C ((196 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3)
def q00015 : UPoly := 0
lemma mod_a00015 : Modulo (spec a00015) r00015 := by
  have h : Modulo (spec a00015) ((Polynomial.C ((-1 : ℂ) / (6 : ℂ)) * r00000 ^ 3 * r00001 ^ 1 * r00003 ^ 1 * r00004 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 1)) := by
    unfold a00015
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (6 : ℂ)))).mul (mod_a00000.pow 3)).mul (mod_a00001.pow 1)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 1)))
  apply h.trans
  refine ⟨q00015, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00015, r00015, r00000, r00001, r00003, r00004, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00017 : UPoly := (Polynomial.C ((520 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00017 : UPoly := 0
lemma mod_a00017 : Modulo (spec a00017) r00017 := by
  have h : Modulo (spec a00017) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1) + (Polynomial.C ((3 : ℂ) / (1 : ℂ)) * r00014 ^ 1)) := by
    unfold a00017
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).add ((Modulo.refl (Polynomial.C ((3 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 1)))
  apply h.trans
  refine ⟨q00017, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00017, r00017, r00009, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00018 : UPoly := (Polynomial.C ((4419910120 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((202575278 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1034128 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((412159936 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4907488 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((17840 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00018 : UPoly := (Polynomial.C ((4276498 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((35936 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((18784 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((88 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00018 : Modulo (spec a00018) r00018 := by
  have h : Modulo (spec a00018) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00008 ^ 1 * r00014 ^ 3) + (Polynomial.C ((1 : ℂ) / (12 : ℂ)) * r00000 ^ 4 * r00001 ^ 1 * r00002 ^ 3 * r00003 ^ 2 * r00004 ^ 1 * r00005 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00017 ^ 1)) := by
    unfold a00018
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00008.pow 1)).mul (mod_a00014.pow 3)).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (12 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 2))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00017.pow 1)))
  apply h.trans
  refine ⟨q00018, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00018, r00018, r00000, r00001, r00002, r00003, r00004, r00005, r00008, r00014, r00017, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00019 : UPoly := (Polynomial.C ((37712 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1160 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-351 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((2312 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1280 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00019 : UPoly := (Polynomial.C ((16 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00019 : Modulo (spec a00019) r00019 := by
  have h : Modulo (spec a00019) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 3 * r00005 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 5 * r00001 ^ 2 * r00003 ^ 1 * r00004 ^ 2 * r00014 ^ 1) + (Polynomial.C ((1 : ℂ) / (6 : ℂ)) * r00000 ^ 5 * r00001 ^ 2 * r00003 ^ 1 * r00004 ^ 2 * r00009 ^ 1)) := by
    unfold a00019
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 3)).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 2)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 2)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 2)).mul (mod_a00014.pow 1))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (6 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 2)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 2)).mul (mod_a00009.pow 1)))
  apply h.trans
  refine ⟨q00019, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00019, r00019, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00025 : UPoly := (Polynomial.C ((128 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00025 : UPoly := 0
lemma mod_a00025 : Modulo (spec a00025) r00025 := by
  have h : Modulo (spec a00025) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 1)) := by
    unfold a00025
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 1)))
  apply h.trans
  refine ⟨q00025, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00025, r00025, r00009, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00026 : UPoly := (Polynomial.C ((-2548679344385364200720 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-365986501537785284812 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-7058268542958199600 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-983250859569672175412 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-39331338968537878198 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2632616383218824 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00026 : UPoly := (Polynomial.C ((-32649640256041644020 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1079492667530577664 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-4772201025926528 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-351728220551860490 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-9015097098023056 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-87234898978808 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-135339671371136 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-422148311776 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((11496683776 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-18313867904 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((7576330240 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((13107200 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((4194304000 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a00026 : Modulo (spec a00026) r00026 := by
  have h : Modulo (spec a00026) ((Polynomial.C ((-1 : ℂ) / (12 : ℂ)) * r00000 ^ 4 * r00001 ^ 1 * r00003 ^ 2 * r00004 ^ 1 * r00018 ^ 1 * r00019 ^ 1 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00018 ^ 2) + (Polynomial.C ((1 : ℂ) / (108 : ℂ)) * r00000 ^ 3 * r00003 ^ 3 * r00019 ^ 3)) := by
    unfold a00026
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (12 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 1)).mul (mod_a00018.pow 1)).mul (mod_a00019.pow 1)).mul (mod_a00025.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00018.pow 2))).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (108 : ℂ)))).mul (mod_a00000.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00019.pow 3)))
  apply h.trans
  refine ⟨q00026, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00026, r00026, r00000, r00001, r00003, r00004, r00009, r00018, r00019, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00027 : UPoly := (Polynomial.C ((-460955515520 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((101172059333360 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((388536598420 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-74325908416 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6806794520704 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((103988490478 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00027 : UPoly := (Polynomial.C ((-2711364128 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((107439764428 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-849336640 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-45541184 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-325044992 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-26952256 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-40960 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-6553600 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00027 : Modulo (spec a00027) r00027 := by
  have h : Modulo (spec a00027) ((Polynomial.C ((-3 : ℂ) / (2 : ℂ)) * r00000 ^ 1 * r00001 ^ 1 * r00004 ^ 1 * r00009 ^ 1 * r00018 ^ 1 * r00025 ^ 1) + (Polynomial.C ((-1 : ℂ) / (8 : ℂ)) * r00000 ^ 5 * r00001 ^ 2 * r00003 ^ 2 * r00004 ^ 2 * r00019 ^ 1 * r00025 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 1 * r00009 ^ 1 * r00019 ^ 2)) := by
    unfold a00027
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-3 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00018.pow 1)).mul (mod_a00025.pow 1)).add (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (8 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 2)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00019.pow 1)).mul (mod_a00025.pow 2))).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00019.pow 2)))
  apply h.trans
  refine ⟨q00027, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00027, r00027, r00000, r00001, r00003, r00004, r00009, r00018, r00019, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00028 : UPoly := (Polynomial.C ((197 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0)
def q00028 : UPoly := 0
lemma mod_a00028 : Modulo (spec a00028) r00028 := by
  have h : Modulo (spec a00028) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00001 ^ 3 * r00002 ^ 1 * r00004 ^ 1 * r00005 ^ 1)) := by
    unfold a00028
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00001.pow 3)).mul (mod_a00002.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)))
  apply h.trans
  refine ⟨q00028, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00028, r00028, r00001, r00002, r00004, r00005, r00006, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00029 : UPoly := (Polynomial.C ((4268265784 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((196790810 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1013488 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((397999561 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4325296 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((12902 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00029 : UPoly := (Polynomial.C ((4129318 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((25868 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((18280 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((40 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00029 : Modulo (spec a00029) r00029 := by
  have h : Modulo (spec a00029) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 3 * r00028 ^ 1) + (Polynomial.C ((1 : ℂ) / (36 : ℂ)) * r00000 ^ 4 * r00001 ^ 1 * r00002 ^ 3 * r00003 ^ 2 * r00004 ^ 1 * r00005 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00017 ^ 1)) := by
    unfold a00029
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 3)).mul (mod_a00028.pow 1)).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (36 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 2))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00017.pow 1)))
  apply h.trans
  refine ⟨q00029, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00029, r00029, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00017, r00028, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00030 : UPoly := (Polynomial.C ((-264323725664 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24837732544 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-85791290 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-52857252416 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-128760124 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8408320 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00030 : UPoly := (Polynomial.C ((-274470928 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-10406848 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-38752 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-327680 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00030 : Modulo (spec a00030) r00030 := by
  have h : Modulo (spec a00030) ((Polynomial.C ((-1 : ℂ) / (36 : ℂ)) * r00000 ^ 4 * r00001 ^ 1 * r00003 ^ 2 * r00004 ^ 1 * r00019 ^ 1 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00018 ^ 1)) := by
    unfold a00030
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (36 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 1)).mul (mod_a00019.pow 1)).mul (mod_a00025.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00018.pow 1)))
  apply h.trans
  refine ⟨q00030, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00030, r00030, r00000, r00001, r00003, r00004, r00009, r00018, r00019, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00031 : UPoly := (Polynomial.C ((-2304640 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-182944 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((408388 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-122689 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1800 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-48454 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00031 : UPoly := (Polynomial.C ((-1968 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2560 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00031 : Modulo (spec a00031) r00031 := by
  have h : Modulo (spec a00031) ((Polynomial.C ((-1 : ℂ) / (6 : ℂ)) * r00000 ^ 5 * r00001 ^ 2 * r00003 ^ 1 * r00004 ^ 2 * r00025 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00019 ^ 1)) := by
    unfold a00031
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (6 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 2)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 2)).mul (mod_a00025.pow 2)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00019.pow 1)))
  apply h.trans
  refine ⟨q00031, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00031, r00031, r00000, r00001, r00003, r00004, r00009, r00019, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00032 : UPoly := (Polynomial.C ((324 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00032 : UPoly := 0
lemma mod_a00032 : Modulo (spec a00032) r00032 := by
  have h : Modulo (spec a00032) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * r00014 ^ 1)) := by
    unfold a00032
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).add ((Modulo.refl (Polynomial.C ((2 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 1)))
  apply h.trans
  refine ⟨q00032, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00032, r00032, r00009, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00033 : UPoly := (Polynomial.C ((-120623200286459570992 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1257343136082959907364 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((32863593426198225656 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-196686655473784268350 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-163740053668611799136 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-53439505978579413500 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00033 : UPoly := (Polynomial.C ((-20042542096862746108 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-126081639547808169584 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-4307052078770632610 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-19015306195316704 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1328544129580880140 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((587990996016417152 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((5386929034616192 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((181679859716262656 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((5172480228412480 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((79146174538240 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((319716031980544 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((3805112568832 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((13830709760 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a00033 : Modulo (spec a00033) r00033 := by
  have h : Modulo (spec a00033) ((Polynomial.C ((-1 : ℂ) / (6 : ℂ)) * r00000 ^ 5 * r00001 ^ 2 * r00003 ^ 2 * r00004 ^ 2 * r00018 ^ 1 * r00031 ^ 1 * r00032 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00027 ^ 1 * r00029 ^ 1) + (Polynomial.C ((3 : ℂ) / (2 : ℂ)) * r00000 ^ 1 * r00001 ^ 1 * r00004 ^ 1 * r00018 ^ 1 * r00025 ^ 1 * r00030 ^ 1)) := by
    unfold a00033
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (6 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 2)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00018.pow 1)).mul (mod_a00031.pow 1)).mul (mod_a00032.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00027.pow 1)).mul (mod_a00029.pow 1))).add (((((((Modulo.refl (Polynomial.C ((3 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00018.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00030.pow 1)))
  apply h.trans
  refine ⟨q00033, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00033, r00033, r00000, r00001, r00003, r00004, r00018, r00025, r00027, r00029, r00030, r00031, r00032, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00034 : UPoly := (Polynomial.C ((8210984768 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6786902229776 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-105743126080 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((477329696 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-211416442478 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-656670752 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00034 : UPoly := (Polynomial.C ((7322384 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-11833984 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((11837728 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((20480 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((3276800 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a00034 : Modulo (spec a00034) r00034 := by
  have h : Modulo (spec a00034) ((Polynomial.C ((-6 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00001 ^ 1 * r00004 ^ 1 * r00018 ^ 1 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 1 * r00019 ^ 2)) := by
    unfold a00034
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-6 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00018.pow 1)).mul (mod_a00025.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 1)).mul (mod_a00019.pow 2)))
  apply h.trans
  refine ⟨q00034, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00034, r00034, r00000, r00001, r00003, r00004, r00018, r00019, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00035 : UPoly := (Polynomial.C ((512 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((4 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
def q00035 : UPoly := 0
lemma mod_a00035 : Modulo (spec a00035) r00035 := by
  have h : Modulo (spec a00035) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 2 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (54 : ℂ)) * r00000 ^ 3 * r00002 ^ 9 * r00003 ^ 3 * r00005 ^ 3)) := by
    unfold a00035
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 2)).mul (mod_a00025.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (54 : ℂ)))).mul (mod_a00000.pow 3)).mul (mod_a00002.pow 9)).mul (mod_a00003.pow 3)).mul (mod_a00005.pow 3)))
  apply h.trans
  refine ⟨q00035, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00035, r00035, r00000, r00002, r00003, r00005, r00007, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00036 : UPoly := (Polynomial.C ((37888 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((388 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((776 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-128 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00036 : UPoly := (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a00036 : Modulo (spec a00036) r00036 := by
  have h : Modulo (spec a00036) ((Polynomial.C ((-1 : ℂ) / (8 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00007 ^ 1 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00014 ^ 2)) := by
    unfold a00036
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (8 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00025.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)))
  apply h.trans
  refine ⟨q00036, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00036, r00036, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00014, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00037 : UPoly := (Polynomial.C ((-332 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00037 : UPoly := 0
lemma mod_a00037 : Modulo (spec a00037) r00037 := by
  have h : Modulo (spec a00037) ((Polynomial.C ((-1 : ℂ) / (3 : ℂ)) * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1)) := by
    unfold a00037
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-1 : ℂ) / (3 : ℂ)))).mul (mod_a00025.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)))
  apply h.trans
  refine ⟨q00037, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00037, r00037, r00009, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00038 : UPoly := (Polynomial.C ((-536 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00038 : UPoly := 0
lemma mod_a00038 : Modulo (spec a00038) r00038 := by
  have h : Modulo (spec a00038) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00037 ^ 1)) := by
    unfold a00038
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00037.pow 1)))
  apply h.trans
  refine ⟨q00038, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00038, r00038, r00009, r00037, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00039 : UPoly := (Polynomial.C ((-2487680 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-63072 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-241220 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-131137 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1832 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((22458 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00039 : UPoly := (Polynomial.C ((-672 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1824 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((16 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((16 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
lemma mod_a00039 : Modulo (spec a00039) r00039 := by
  have h : Modulo (spec a00039) ((Polynomial.C ((-1 : ℂ) / (2 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00007 ^ 1 * r00009 ^ 1 * r00032 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00036 ^ 1) + (Polynomial.C ((3 : ℂ) / (8 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00007 ^ 1 * r00025 ^ 1 * r00038 ^ 1)) := by
    unfold a00039
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00032.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00036.pow 1))).add (((((((Modulo.refl (Polynomial.C ((3 : ℂ) / (8 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00038.pow 1)))
  apply h.trans
  refine ⟨q00039, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00039, r00039, r00000, r00003, r00004, r00007, r00009, r00025, r00032, r00036, r00038, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00040 : UPoly := (Polynomial.C ((65024 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((2720 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((5440 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((32 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4)
def q00040 : UPoly := (Polynomial.C ((32 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a00040 : Modulo (spec a00040) r00040 := by
  have h : Modulo (spec a00040) ((Polynomial.C ((-8 : ℂ) / (3 : ℂ)) * r00009 ^ 1 * r00032 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00025 ^ 2)) := by
    unfold a00040
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((-8 : ℂ) / (3 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00032.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1))).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 2)))
  apply h.trans
  refine ⟨q00040, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00040, r00040, r00009, r00025, r00032, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00041 : UPoly := (Polynomial.C ((-606816256 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-47348480 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-33449920 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-869067520 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-12511360 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4387360 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00041 : UPoly := (Polynomial.C ((-1407488 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-27712 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((736768 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-44672 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((21760 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((128 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00041 : Modulo (spec a00041) r00041 := by
  have h : Modulo (spec a00041) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00007 ^ 1 * r00009 ^ 1 * r00014 ^ 2 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 8 * r00002 ^ 5 * r00003 ^ 4 * r00004 ^ 1 * r00005 ^ 1 * r00040 ^ 1)) := by
    unfold a00041
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2)).mul (mod_a00025.pow 1)).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 8)).mul (mod_a00002.pow 5)).mul (mod_a00003.pow 4)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00040.pow 1)))
  apply h.trans
  refine ⟨q00041, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00041, r00041, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00025, r00040, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00042 : UPoly := (Polynomial.C ((4224938944 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((195401504 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1010944 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((393953755 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4065520 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((10514 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00042 : UPoly := (Polynomial.C ((4087264 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((20996 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((18136 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((16 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00042 : Modulo (spec a00042) r00042 := by
  have h : Modulo (spec a00042) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1 * r00014 ^ 3) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00017 ^ 1)) := by
    unfold a00042
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)).mul (mod_a00014.pow 3)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00017.pow 1)))
  apply h.trans
  refine ⟨q00042, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00042, r00042, r00000, r00001, r00003, r00004, r00006, r00014, r00017, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00043 : UPoly := (Polynomial.C ((8449877888 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((128921152 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-659968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((787900598 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((2767328 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6620 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00043 : UPoly := (Polynomial.C ((-1024 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1)
lemma mod_a00043 : Modulo (spec a00043) r00043 := by
  have h : Modulo (spec a00043) ((Polynomial.C ((-1 : ℂ) / (4 : ℂ)) * r00000 ^ 1 * r00001 ^ 4 * r00004 ^ 2 * r00007 ^ 1 * r00014 ^ 2 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 5 * r00003 ^ 1 * r00005 ^ 1 * r00042 ^ 1)) := by
    unfold a00043
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (4 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 4)).mul (mod_a00004.pow 2)).mul (mod_a00007.pow 1)).mul (mod_a00014.pow 2)).mul (mod_a00025.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00043, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00043, r00043, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00014, r00025, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00044 : UPoly := (Polynomial.C ((-505449778880 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-15430251280 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((345879968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101032697072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-353784374 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((3829216 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00044 : UPoly := (Polynomial.C ((-1571407216 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-5534656 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((13240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00044 : Modulo (spec a00044) r00044 := by
  have h : Modulo (spec a00044) ((Polynomial.C ((-1 : ℂ) / (4 : ℂ)) * r00000 ^ 1 * r00001 ^ 3 * r00004 ^ 2 * r00041 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00043 ^ 1)) := by
    unfold a00044
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (4 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 3)).mul (mod_a00004.pow 2)).mul (mod_a00041.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00043.pow 1)))
  apply h.trans
  refine ⟨q00044, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00044, r00044, r00000, r00001, r00004, r00009, r00041, r00043, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00045 : UPoly := (Polynomial.C ((-14229472 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1109960 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((20096 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-6772430 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-32542 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((2540 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00045 : UPoly := (Polynomial.C ((-32824 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-146 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-4 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
lemma mod_a00045 : Modulo (spec a00045) r00045 := by
  have h : Modulo (spec a00045) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00007 ^ 1 * r00009 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (144 : ℂ)) * r00000 ^ 8 * r00002 ^ 5 * r00003 ^ 4 * r00004 ^ 1 * r00005 ^ 1 * r00037 ^ 1)) := by
    unfold a00045
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2)).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (144 : ℂ)))).mul (mod_a00000.pow 8)).mul (mod_a00002.pow 5)).mul (mod_a00003.pow 4)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00037.pow 1)))
  apply h.trans
  refine ⟨q00045, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00045, r00045, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00037, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00046 : UPoly := (Polynomial.C ((-505234994816 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-113766402784 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2211330784 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101103048560 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-5558177846 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-21171040 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00046 : UPoly := (Polynomial.C ((-542384 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-11008 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-32 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((319232 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6080 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((12416 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((64 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((64 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00046 : Modulo (spec a00046) r00046 := by
  have h : Modulo (spec a00046) ((Polynomial.C ((-1 : ℂ) / (72 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00002 ^ 5 * r00003 ^ 4 * r00004 ^ 3 * r00005 ^ 1 * r00009 ^ 1 * r00032 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00044 ^ 1) + (Polynomial.C ((3 : ℂ) / (2 : ℂ)) * r00000 ^ 1 * r00001 ^ 3 * r00004 ^ 2 * r00025 ^ 1 * r00045 ^ 1)) := by
    unfold a00046
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00002.pow 5)).mul (mod_a00003.pow 4)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00032.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00044.pow 1))).add ((((((Modulo.refl (Polynomial.C ((3 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 3)).mul (mod_a00004.pow 2)).mul (mod_a00025.pow 1)).mul (mod_a00045.pow 1)))
  apply h.trans
  refine ⟨q00046, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00046, r00046, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00025, r00032, r00044, r00045, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00047 : UPoly := (Polynomial.C ((-64672878553088 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6354135075328 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-69457241984 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-12944346739744 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-242965146368 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1106118976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00047 : UPoly := (Polynomial.C ((-67233777152 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-685349120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((19100704 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((138752 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6669056 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((229888 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((87040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((512 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 8)
lemma mod_a00047 : Modulo (spec a00047) r00047 := by
  have h : Modulo (spec a00047) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1 * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (36 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00014 ^ 2 * r00040 ^ 1)) := by
    unfold a00047
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (36 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a00040.pow 1)))
  apply h.trans
  refine ⟨q00047, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00047, r00047, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00025, r00040, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00048 : UPoly := (Polynomial.C ((103936 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((4288 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((8576 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((64 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4)
def q00048 : UPoly := 0
lemma mod_a00048 : Modulo (spec a00048) r00048 := by
  have h : Modulo (spec a00048) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1) + (Polynomial.C ((2 : ℂ) / (3 : ℂ)) * r00040 ^ 1)) := by
    unfold a00048
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).add ((Modulo.refl (Polynomial.C ((2 : ℂ) / (3 : ℂ)))).mul (mod_a00040.pow 1)))
  apply h.trans
  refine ⟨q00048, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00048, r00048, r00009, r00025, r00040, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00049 : UPoly := (Polynomial.C ((-64673084391424 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6500287652864 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-73246430720 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-12944392904768 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-223309017856 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-205114240 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00049 : UPoly := (Polynomial.C ((4678144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((369060352 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((20318240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((124928 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((5268224 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((202240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((68608 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((512 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 8)
lemma mod_a00049 : Modulo (spec a00049) r00049 := by
  have h : Modulo (spec a00049) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00047 ^ 1) + (Polynomial.C ((1 : ℂ) / (24 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00014 ^ 2 * r00048 ^ 1)) := by
    unfold a00049
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00047.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (24 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a00048.pow 1)))
  apply h.trans
  refine ⟨q00049, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00049, r00049, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00047, r00048, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00050 : UPoly := (Polynomial.C ((-129345507067904 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-12523966448128 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-134286415744 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-25888639314976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-510472357376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-315195200 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00050 : UPoly := (Polynomial.C ((-201707014144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2081546240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-5383168 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00050 : Modulo (spec a00050) r00050 := by
  have h : Modulo (spec a00050) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1 * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00047 ^ 1)) := by
    unfold a00050
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00047.pow 1)))
  apply h.trans
  refine ⟨q00050, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00050, r00050, r00007, r00009, r00025, r00042, r00047, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00051 : UPoly := (Polynomial.C ((-64672863819776 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6341418033664 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-69177615488 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-12944344073248 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-244593791744 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1150699840 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00051 : UPoly := 0
lemma mod_a00051 : Modulo (spec a00051) r00051 := by
  have h : Modulo (spec a00051) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00049 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00050 ^ 1)) := by
    unfold a00051
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00049.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00050.pow 1)))
  apply h.trans
  refine ⟨q00051, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00051, r00051, r00049, r00050, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00052 : UPoly := (Polynomial.C ((-505254783904 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-48076232864 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-503959514 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-33709087792 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-703975298 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4655392 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00052 : UPoly := (Polynomial.C ((-525279640 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1912598 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-5992 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-4 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-11968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00052 : Modulo (spec a00052) r00052 := by
  have h : Modulo (spec a00052) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1 * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00014 ^ 2 * r00037 ^ 1)) := by
    unfold a00052
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a00037.pow 1)))
  apply h.trans
  refine ⟨q00052, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00052, r00052, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00037, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00053 : UPoly := (Polynomial.C ((-505254542432 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-47851306240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-166418842 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-33709073392 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-715558498 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-14760032 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00053 : UPoly := (Polynomial.C ((-5488 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1703948 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-22720 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-22912 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-16 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-32 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00053 : Modulo (spec a00053) r00053 := by
  have h : Modulo (spec a00053) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00052 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00014 ^ 2 * r00038 ^ 1)) := by
    unfold a00053
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00052.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a00038.pow 1)))
  apply h.trans
  refine ⟨q00053, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00053, r00053, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00038, r00052, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00054 : UPoly := (Polynomial.C ((-252668185760 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24102370168 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-84414352 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-50522240504 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-116055043 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6759280 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00054 : UPoly := (Polynomial.C ((-29147864 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8126944 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-21028 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-327680 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00054 : Modulo (spec a00054) r00054 := by
  have h : Modulo (spec a00054) ((Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00025 ^ 1 * r00032 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1)) := by
    unfold a00054
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00025.pow 1)).mul (mod_a00032.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00054, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00054, r00054, r00000, r00001, r00003, r00004, r00009, r00025, r00032, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00055 : UPoly := (Polynomial.C ((-505336256416 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-48105388448 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-168100510 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101044460176 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-700571522 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-13866848 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00055 : UPoly := (Polynomial.C ((-872 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-250882 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-3616 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-4 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1216 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00055 : Modulo (spec a00055) r00055 := by
  have h : Modulo (spec a00055) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1 * r00054 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00009 ^ 1 * r00014 ^ 2)) := by
    unfold a00055
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).mul (mod_a00054.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2)))
  apply h.trans
  refine ⟨q00055, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00055, r00055, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00054, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00056 : UPoly := (Polynomial.C ((-505336014944 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-47880461824 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-499598542 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101044416976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-712154722 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-14660704 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00056 : UPoly := (Polynomial.C ((-5488 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1703948 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-22720 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-8 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-22912 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-16 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-32 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00056 : Modulo (spec a00056) r00056 := by
  have h : Modulo (spec a00056) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00055 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00014 ^ 2 * r00038 ^ 1)) := by
    unfold a00056
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00055.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a00038.pow 1)))
  apply h.trans
  refine ⟨q00056, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00056, r00056, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00038, r00055, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00057 : UPoly := (Polynomial.C ((-1010590557376 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-95731768064 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-998855068 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-202171637152 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1427713220 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-9806912 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00057 : UPoly := 0
lemma mod_a00057 : Modulo (spec a00057) r00057 := by
  have h : Modulo (spec a00057) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00053 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00056 ^ 1)) := by
    unfold a00057
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00053.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00056.pow 1)))
  apply h.trans
  refine ⟨q00057, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00057, r00057, r00053, r00056, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00058 : UPoly := (Polynomial.C ((-37888 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-388 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-776 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4)
def q00058 : UPoly := (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a00058 : Modulo (spec a00058) r00058 := by
  have h : Modulo (spec a00058) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00025 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00032 ^ 1)) := by
    unfold a00058
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 2)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00032.pow 1)))
  apply h.trans
  refine ⟨q00058, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00058, r00058, r00009, r00025, r00032, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00059 : UPoly := (Polynomial.C ((-2237760 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-180896 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((818120 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-119937 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1792 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-96902 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00059 : UPoly := (Polynomial.C ((-8512 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-44 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-6208 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-56 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00059 : Modulo (spec a00059) r00059 := by
  have h : Modulo (spec a00059) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00009 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00007 ^ 1 * r00058 ^ 1)) := by
    unfold a00059
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00059, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00059, r00059, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00058, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00060 : UPoly := (Polynomial.C ((-6713280 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-180896 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((818120 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-359811 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-5376 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-290706 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00060 : UPoly := (Polynomial.C ((-17024 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-88 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-12416 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-112 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00060 : Modulo (spec a00060) r00060 := by
  have h : Modulo (spec a00060) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00059 ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00009 ^ 1 * r00014 ^ 2) + (Polynomial.C ((2 : ℂ) / (3 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00007 ^ 1 * r00058 ^ 1)) := by
    unfold a00060
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00059.pow 1)).add ((((((Modulo.refl (Polynomial.C ((2 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2))).add ((((((Modulo.refl (Polynomial.C ((2 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00007.pow 1)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00060, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00060, r00060, r00000, r00001, r00002, r00003, r00004, r00005, r00007, r00009, r00014, r00058, r00059, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00061 : UPoly := (Polynomial.C ((-64498125618688 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6041726684288 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-62267184992 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-13021767201016 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-96690230656 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-717024400 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00061 : UPoly := (Polynomial.C ((-4195497856 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1012681088 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((19535384 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((731160448 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((2694208 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((28672 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((1550432 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00061 : Modulo (spec a00061) r00061 := by
  have h : Modulo (spec a00061) ((Polynomial.C ((-1 : ℂ) / (3 : ℂ)) * r00051 ^ 1) + (Polynomial.C ((-1 : ℂ) / (54 : ℂ)) * r00000 ^ 4 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00032 ^ 1 * r00060 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00025 ^ 1 * r00057 ^ 1)) := by
    unfold a00061
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (3 : ℂ)))).mul (mod_a00051.pow 1)).add (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (54 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00032.pow 1)).mul (mod_a00060.pow 1))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 1)).mul (mod_a00057.pow 1)))
  apply h.trans
  refine ⟨q00061, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00061, r00061, r00000, r00001, r00003, r00004, r00025, r00032, r00051, r00057, r00060, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00062 : UPoly := (Polynomial.C ((-1722623562940928 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-74905262950101376 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-84882031459328 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-431411147600768 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((7615523482836128 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((237253707204608 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5)
def q00062 : UPoly := (Polynomial.C ((-8143405543040 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((62873902680064 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4351265415424 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-28738152608 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((8571120812032 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((138887155648 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-94866944 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-3630848 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-8192 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00062 : Modulo (spec a00062) r00062 := by
  have h : Modulo (spec a00062) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00014 ^ 4 * r00025 ^ 1) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00040 ^ 1 * r00042 ^ 1)) := by
    unfold a00062
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 4)).mul (mod_a00025.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00040.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00062, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00062, r00062, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00025, r00040, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00063 : UPoly := (Polynomial.C ((-1848529484121088 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-149629643910109952 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-169672370672128 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-464782393652992 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((15241665922531648 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((474608490029824 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5)
def q00063 : UPoly := (Polynomial.C ((2861498208640 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((62896901903872 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4351684448512 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((110554517344 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((8572804907008 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((138892132288 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((749171200 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((1345792 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00063 : Modulo (spec a00063) r00063 := by
  have h : Modulo (spec a00063) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00062 ^ 1) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00040 ^ 1 * r00042 ^ 1)) := by
    unfold a00063
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00062.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00040.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00063, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00063, r00063, r00000, r00002, r00003, r00040, r00042, r00062, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00064 : UPoly := (Polynomial.C ((-10749708418048 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1026247698304 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-32361682912 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-6510895774720 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-134652490816 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-872760832 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00064 : UPoly := (Polynomial.C ((-102835075328 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1072523296 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2851840 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((323581696 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4839424 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((22144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((10108960 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((30208 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((64 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((91136 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((128 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((256 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a00064 : Modulo (spec a00064) r00064 := by
  have h : Modulo (spec a00064) ((Polynomial.C ((-1 : ℂ) / (54 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00009 ^ 1 * r00032 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00025 ^ 2 * r00032 ^ 1)) := by
    unfold a00064
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (54 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00009.pow 1)).mul (mod_a00032.pow 2)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1))).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00025.pow 2)).mul (mod_a00032.pow 1)))
  apply h.trans
  refine ⟨q00064, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00064, r00064, r00000, r00001, r00003, r00004, r00009, r00025, r00032, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00065 : UPoly := (Polynomial.C ((-521462325160960 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((6815456870696704 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((193454966280704 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-130191253237760 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-224445781301248 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-22509196779776 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00065 : UPoly := (Polynomial.C ((-3913230540544 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-52156163869184 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1077638959616 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-53412976640 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-6930432 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-20480 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-3473408 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-20480 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-8192 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00065 : Modulo (spec a00065) r00065 := by
  have h : Modulo (spec a00065) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00014 ^ 4 * r00025 ^ 1) + (Polynomial.C ((2 : ℂ) / (3 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00064 ^ 1)) := by
    unfold a00065
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 4)).mul (mod_a00025.pow 1)).add (((((Modulo.refl (Polynomial.C ((2 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00064.pow 1)))
  apply h.trans
  refine ⟨q00065, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00065, r00065, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00025, r00064, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00066 : UPoly := (Polynomial.C ((-3287010538423808 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-54458892338011264 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-570483316853248 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-821984907314048 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((5595511451124896 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((169726116865280 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5)
def q00066 : UPoly := 0
lemma mod_a00066 : Modulo (spec a00066) r00066 := by
  have h : Modulo (spec a00066) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00062 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00065 ^ 1)) := by
    unfold a00066
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00062.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00065.pow 1)))
  apply h.trans
  refine ⟨q00066, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00066, r00066, r00062, r00065, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00067 : UPoly := (Polynomial.C ((-570615558060544 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-22676504027569024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2097534652902400 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-428922433655680 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6945725791218848 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((71592734099456 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00067 : UPoly := 0
lemma mod_a00067 : Modulo (spec a00067) r00067 := by
  have h : Modulo (spec a00067) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00063 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00066 ^ 1)) := by
    unfold a00067
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00063.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00066.pow 1)))
  apply h.trans
  refine ⟨q00067, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00067, r00067, r00063, r00066, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00068 : UPoly := (Polynomial.C ((-658145135100416 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-74784674956706176 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-84820903294976 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-166051213235072 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((7622602787409056 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((237321090951680 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00068 : UPoly := (Polynomial.C ((2861498208640 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((62896901903872 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4351684448512 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((110554517344 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((8572804907008 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((138892132288 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((749171200 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((1345792 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00068 : Modulo (spec a00068) r00068 := by
  have h : Modulo (spec a00068) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00063 ^ 1) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00040 ^ 1 * r00042 ^ 1)) := by
    unfold a00068
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00063.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00040.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00068, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00068, r00068, r00000, r00002, r00003, r00040, r00042, r00063, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00069 : UPoly := (Polynomial.C ((-2369991809282048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-142814187039413248 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-4387699041866752 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-198324548963584 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((14568328578627904 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((452099293250048 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00069 : UPoly := 0
lemma mod_a00069 : Modulo (spec a00069) r00069 := by
  have h : Modulo (spec a00069) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00067 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00068 ^ 1)) := by
    unfold a00069
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00067.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00068.pow 1)))
  apply h.trans
  refine ⟨q00069, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00069, r00069, r00067, r00068, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00070 : UPoly := (Polynomial.C ((-1361227600000 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5876615035888 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1362769393324 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1020158863166 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-7011189544496 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-60090159610 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00070 : UPoly := (Polynomial.C ((-10116777376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-404773062820 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-7313747074 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-405994736 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1577297936 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-16266400 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-774728 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-160 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-64 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00070 : Modulo (spec a00070) r00070 := by
  have h : Modulo (spec a00070) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00014 ^ 4) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00037 ^ 1 * r00042 ^ 1)) := by
    unfold a00070
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 4)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00037.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00070, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00070, r00070, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00037, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00071 : UPoly := (Polynomial.C ((-1336415580416 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((11805568610576 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2731985897732 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1003755482716 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-13994725555504 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-120092579966 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00071 : UPoly := (Polynomial.C ((-563909536 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-404234018512 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-7310473378 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-43253408 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1575836048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-16262080 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-42056 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00071 : Modulo (spec a00071) r00071 := by
  have h : Modulo (spec a00071) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00070 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00037 ^ 1 * r00042 ^ 1)) := by
    unfold a00071
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00070.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00037.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00071, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00071, r00071, r00000, r00002, r00003, r00037, r00042, r00070, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00072 : UPoly := (Polynomial.C ((-1364943863936 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((13181335325648 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((374642226148 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-340688409194 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1323124478480 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-44114498042 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00072 : UPoly := (Polynomial.C ((-10032316832 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-101224162444 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-232231334 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-134432336 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-54144 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-160 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-27136 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-160 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-64 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00072 : Modulo (spec a00072) r00072 := by
  have h : Modulo (spec a00072) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00014 ^ 4) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00054 ^ 1)) := by
    unfold a00072
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 4)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00054.pow 1)))
  apply h.trans
  refine ⟨q00072, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00072, r00072, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00054, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00073 : UPoly := (Polynomial.C ((-908723821312 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((30811180433312 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2486696071768 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2042224090748 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-10980562979936 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-34734885884 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00073 : UPoly := 0
lemma mod_a00073 : Modulo (spec a00073) r00073 := by
  have h : Modulo (spec a00073) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00070 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00072 ^ 1)) := by
    unfold a00073
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00070.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00072.pow 1)))
  apply h.trans
  refine ⟨q00073, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00073, r00073, r00070, r00072, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00074 : UPoly := (Polynomial.C ((-4062587044352 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((66227886265040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1739560656500 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1015326524488 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-8325096178480 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-224297237618 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00074 : UPoly := 0
lemma mod_a00074 : Modulo (spec a00074) r00074 := by
  have h : Modulo (spec a00074) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00071 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00073 ^ 1)) := by
    unfold a00074
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00071.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00073.pow 1)))
  apply h.trans
  refine ⟨q00074, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00074, r00074, r00071, r00073, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00075 : UPoly := (Polynomial.C ((-1343848108288 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((26519686267696 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((751433489324 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-335856070516 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2637031112464 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-88141256830 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00075 : UPoly := (Polynomial.C ((-479448992 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-101044481008 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-232110086 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-13518560 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00075 : Modulo (spec a00075) r00075 := by
  have h : Modulo (spec a00075) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00072 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00054 ^ 1)) := by
    unfold a00075
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00072.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00054.pow 1)))
  apply h.trans
  refine ⟨q00075, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00075, r00075, r00000, r00002, r00003, r00054, r00072, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00076 : UPoly := (Polynomial.C ((-4070019572224 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((6370096300112 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4740996539740 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-3049792302296 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-18891656317328 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-192345914482 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00076 : UPoly := 0
lemma mod_a00076 : Modulo (spec a00076) r00076 := by
  have h : Modulo (spec a00076) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00073 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00075 ^ 1)) := by
    unfold a00076
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00073.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00075.pow 1)))
  apply h.trans
  refine ⟨q00076, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00076, r00076, r00073, r00075, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00077 : UPoly := (Polynomial.C ((-2710868872192 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((123558752966048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((9959678509240 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-6095771875760 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-43866944852768 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-138881050700 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00077 : UPoly := 0
lemma mod_a00077 : Modulo (spec a00077) r00077 := by
  have h : Modulo (spec a00077) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00074 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00076 ^ 1)) := by
    unfold a00077
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00074.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00076.pow 1)))
  apply h.trans
  refine ⟨q00077, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00077, r00077, r00074, r00076, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00078 : UPoly := (Polynomial.C ((-252689092096 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24104484224 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-253261808 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-50528073784 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-348097033 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6756304 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00078 : UPoly := (Polynomial.C ((-786517184 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8114528 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-20980 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-96896 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-6208 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00078 : Modulo (spec a00078) r00078 := by
  have h : Modulo (spec a00078) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00058 ^ 1)) := by
    unfold a00078
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00078, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00078, r00078, r00000, r00001, r00003, r00004, r00009, r00042, r00058, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00079 : UPoly := (Polynomial.C ((-126344546048 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-12052242112 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-126630904 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-25264036892 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-348097033 : ℂ) / (6 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-3378152 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00079 : UPoly := (Polynomial.C ((-786517184 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8114528 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-20980 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-96896 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-6208 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00079 : Modulo (spec a00079) r00079 := by
  have h : Modulo (spec a00079) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00078 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00058 ^ 1)) := by
    unfold a00079
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00078.pow 1))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00079, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00079, r00079, r00000, r00001, r00003, r00004, r00009, r00042, r00058, r00078, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00080 : UPoly := (Polynomial.C ((-84270788672 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8037215024 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-253307504 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-16818978536 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-347657737 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6748304 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00080 : UPoly := (Polynomial.C ((2801680 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((11008 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((32 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-193792 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-6080 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-16 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-12416 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-64 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00080 : Modulo (spec a00080) r00080 := by
  have h : Modulo (spec a00080) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00078 ^ 1) + (Polynomial.C ((1 : ℂ) / (108 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00058 ^ 1)) := by
    unfold a00080
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00078.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (108 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00080, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00080, r00080, r00000, r00001, r00003, r00004, r00058, r00078, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00081 : UPoly := (Polynomial.C ((-168541577344 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-16074430048 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-506615008 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-33637957072 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-695315474 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-13496608 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00081 : UPoly := (Polynomial.C ((1400840 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5504 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((16 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-96896 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3040 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-6208 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-32 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00081 : Modulo (spec a00081) r00081 := by
  have h : Modulo (spec a00081) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00079 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00080 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00058 ^ 1)) := by
    unfold a00081
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00079.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00080.pow 1))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00058.pow 1)))
  apply h.trans
  refine ⟨q00081, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00081, r00081, r00000, r00001, r00003, r00004, r00058, r00079, r00080, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00082 : UPoly := (Polynomial.C ((-32835002753536 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1427751212023680 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((121137790765568 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2726708966016 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-513951168423904 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-13983217175296 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00082 : UPoly := (Polynomial.C ((3036725974144 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((188408745652736 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4612604301568 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((118689455968 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((3229459824640 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((22250095168 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((431891456 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00082 : Modulo (spec a00082) r00082 := by
  have h : Modulo (spec a00082) ((Polynomial.C ((-4 : ℂ) / (3 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00032 ^ 1 * r00081 ^ 1) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00069 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00025 ^ 1 * r00077 ^ 1)) := by
    unfold a00082
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-4 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00032.pow 1)).mul (mod_a00081.pow 1)).add ((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00069.pow 1))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 1)).mul (mod_a00077.pow 1)))
  apply h.trans
  refine ⟨q00082, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00082, r00082, r00000, r00002, r00003, r00025, r00032, r00069, r00077, r00081, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00083 : UPoly := (Polynomial.C ((-75335147929600 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-7189906479616 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-226690492288 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-45460021961728 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-939870779776 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6087000064 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00083 : UPoly := (Polynomial.C ((-100853507072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1040773120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2691584 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00083 : Modulo (spec a00083) r00083 := by
  have h : Modulo (spec a00083) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((4 : ℂ) / (3 : ℂ)) * r00064 ^ 1)) := by
    unfold a00083
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((4 : ℂ) / (3 : ℂ)))).mul (mod_a00064.pow 1)))
  apply h.trans
  refine ⟨q00083, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00083, r00083, r00009, r00025, r00042, r00064, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00084 : UPoly := (Polynomial.C ((-107671462187008 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-10274822166016 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-323934252928 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-64876460824576 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1341131596288 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8682956800 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00084 : UPoly := (Polynomial.C ((-100853507072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1040773120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2691584 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00084 : Modulo (spec a00084) r00084 := by
  have h : Modulo (spec a00084) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00083 ^ 1)) := by
    unfold a00084
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00083.pow 1)))
  apply h.trans
  refine ⟨q00084, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00084, r00084, r00009, r00025, r00042, r00083, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00085 : UPoly := (Polynomial.C ((-140007776444416 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-13359737852416 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-421178013568 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-84292899687424 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1742392412800 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-11278913536 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00085 : UPoly := (Polynomial.C ((-100853507072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1040773120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2691584 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00085 : Modulo (spec a00085) r00085 := by
  have h : Modulo (spec a00085) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00084 ^ 1)) := by
    unfold a00085
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00084.pow 1)))
  apply h.trans
  refine ⟨q00085, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00085, r00085, r00009, r00025, r00042, r00084, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00086 : UPoly := (Polynomial.C ((-29583495400448 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2823724318208 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-89034305984 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-17875901265152 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-369620185760 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2394510848 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00086 : UPoly := 0
lemma mod_a00086 : Modulo (spec a00086) r00086 := by
  have h : Modulo (spec a00086) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00064 ^ 1) + (Polynomial.C ((3 : ℂ) / (4 : ℂ)) * r00083 ^ 1)) := by
    unfold a00086
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00064.pow 1)).add ((Modulo.refl (Polynomial.C ((3 : ℂ) / (4 : ℂ)))).mul (mod_a00083.pow 1)))
  apply h.trans
  refine ⟨q00086, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00086, r00086, r00064, r00083, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00087 : UPoly := (Polynomial.C ((-75335147929600 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-7189906479616 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-226690492288 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-45460021961728 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-939870779776 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6087000064 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00087 : UPoly := 0
lemma mod_a00087 : Modulo (spec a00087) r00087 := by
  have h : Modulo (spec a00087) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00084 ^ 1) + (Polynomial.C ((4 : ℂ) / (3 : ℂ)) * r00086 ^ 1)) := by
    unfold a00087
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00084.pow 1)).add ((Modulo.refl (Polynomial.C ((4 : ℂ) / (3 : ℂ)))).mul (mod_a00086.pow 1)))
  apply h.trans
  refine ⟨q00087, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00087, r00087, r00084, r00086, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00088 : UPoly := (Polynomial.C ((-366013220233216 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-34929457291264 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1101249490432 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-220672965572608 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-4562004752128 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-29539913728 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00088 : UPoly := 0
lemma mod_a00088 : Modulo (spec a00088) r00088 := by
  have h : Modulo (spec a00088) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00085 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00087 ^ 1)) := by
    unfold a00088
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00085.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00087.pow 1)))
  apply h.trans
  refine ⟨q00088, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00088, r00088, r00085, r00087, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00089 : UPoly := (Polynomial.C ((-172344090701824 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-16444653538816 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-518421774208 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-103709338550272 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2143653229312 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-13874870272 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00089 : UPoly := (Polynomial.C ((-100853507072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1040773120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2691584 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00089 : Modulo (spec a00089) r00089 := by
  have h : Modulo (spec a00089) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00025 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00085 ^ 1)) := by
    unfold a00089
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00085.pow 1)))
  apply h.trans
  refine ⟨q00089, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00089, r00089, r00009, r00025, r00042, r00085, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00090 : UPoly := (Polynomial.C ((-538357310935040 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-51374110830080 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1619671264640 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-324382304122880 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-6705657981440 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-43414784000 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00090 : UPoly := 0
lemma mod_a00090 : Modulo (spec a00090) r00090 := by
  have h : Modulo (spec a00090) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00088 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00089 ^ 1)) := by
    unfold a00090
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00088.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00089.pow 1)))
  apply h.trans
  refine ⟨q00090, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00090, r00090, r00088, r00089, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00091 : UPoly := (Polynomial.C ((-505295640896 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-48203273968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-506482016 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101085883376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-696481810 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1502176 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00091 : UPoly := (Polynomial.C ((-787918024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8131040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-21028 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00091 : Modulo (spec a00091) r00091 := by
  have h : Modulo (spec a00091) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00054 ^ 1)) := by
    unfold a00091
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00054.pow 1)))
  apply h.trans
  refine ⟨q00091, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00091, r00091, r00009, r00042, r00054, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00092 : UPoly := (Polynomial.C ((-757923096032 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-72304177768 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-759720976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-151649526248 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1044798491 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-20279888 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00092 : UPoly := (Polynomial.C ((-787918024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8131040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-21028 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00092 : Modulo (spec a00092) r00092 := by
  have h : Modulo (spec a00092) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00091 ^ 1)) := by
    unfold a00092
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00091.pow 1)))
  apply h.trans
  refine ⟨q00092, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00092, r00092, r00009, r00042, r00091, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00093 : UPoly := (Polynomial.C ((-1010550551168 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-96405081568 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-112551104 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-202213169120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-464371724 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-27040192 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00093 : UPoly := (Polynomial.C ((-787918024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8131040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-21028 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00093 : Modulo (spec a00093) r00093 := by
  have h : Modulo (spec a00093) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00042 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00092 ^ 1)) := by
    unfold a00093
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00042.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00092.pow 1)))
  apply h.trans
  refine ⟨q00093, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00093, r00093, r00009, r00042, r00092, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00094 : UPoly := (Polynomial.C ((-757963826656 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-72305644136 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-759725072 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-151608123880 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1044646939 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-20278864 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00094 : UPoly := 0
lemma mod_a00094 : Modulo (spec a00094) r00094 := by
  have h : Modulo (spec a00094) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00054 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00091 ^ 1)) := by
    unfold a00094
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00054.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00091.pow 1)))
  apply h.trans
  refine ⟨q00094, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00094, r00094, r00054, r00091, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00095 : UPoly := (Polynomial.C ((-505295640896 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-48203273968 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-506482016 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-101085883376 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-696481810 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1502176 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q00095 : UPoly := 0
lemma mod_a00095 : Modulo (spec a00095) r00095 := by
  have h : Modulo (spec a00095) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00092 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00094 ^ 1)) := by
    unfold a00095
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00092.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00094.pow 1)))
  apply h.trans
  refine ⟨q00095, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00095, r00095, r00092, r00094, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00096 : UPoly := (Polynomial.C ((-2526437473856 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-241014903472 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-844135328 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-505470819248 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-386951178 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-67598944 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00096 : UPoly := 0
lemma mod_a00096 : Modulo (spec a00096) r00096 := by
  have h : Modulo (spec a00096) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00093 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00095 ^ 1)) := by
    unfold a00096
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00093.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00095.pow 1)))
  apply h.trans
  refine ⟨q00096, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00096, r00096, r00093, r00095, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00097 : UPoly := (Polynomial.C ((-112292445824 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-32136004768 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1012968128 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-7486309792 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1392812068 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-27038144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00097 : UPoly := 0
lemma mod_a00097 : Modulo (spec a00097) r00097 := by
  have h : Modulo (spec a00097) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00054 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00094 ^ 1)) := by
    unfold a00097
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00054.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00094.pow 1)))
  apply h.trans
  refine ⟨q00097, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00097, r00097, r00054, r00094, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00098 : UPoly := (Polynomial.C ((-842172978368 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-80339278736 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2532414176 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-168462671504 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3482257498 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-67596896 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00098 : UPoly := 0
lemma mod_a00098 : Modulo (spec a00098) r00098 := by
  have h : Modulo (spec a00098) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00095 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00097 ^ 1)) := by
    unfold a00098
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00095.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00097.pow 1)))
  apply h.trans
  refine ⟨q00098, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00098, r00098, r00095, r00097, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00099 : UPoly := (Polynomial.C ((-5052956408960 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-482032739680 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-5064820160 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1010858833760 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-6964818100 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-15021760 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00099 : UPoly := 0
lemma mod_a00099 : Modulo (spec a00099) r00099 := by
  have h : Modulo (spec a00099) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00096 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00098 ^ 1)) := by
    unfold a00099
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00096.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00098.pow 1)))
  apply h.trans
  refine ⟨q00099, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00099, r00099, r00096, r00098, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00100 : UPoly := (Polynomial.C ((-107497084180480 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-10262476983040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-323616829120 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-65108957747200 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1346524908160 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8727608320 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00100 : UPoly := (Polynomial.C ((-21000573440 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-322744640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1602560 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((3655247360 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((16568320 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((221440 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((103711040 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((302080 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((640 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((496640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((2560 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 10)
lemma mod_a00100 : Modulo (spec a00100) r00100 := by
  have h : Modulo (spec a00100) ((Polynomial.C ((-5 : ℂ) / (27 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00032 ^ 1 * r00058 ^ 1) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00090 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00025 ^ 1 * r00099 ^ 1)) := by
    unfold a00100
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-5 : ℂ) / (27 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00032.pow 1)).mul (mod_a00058.pow 1)).add ((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00090.pow 1))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 1)).mul (mod_a00099.pow 1)))
  apply h.trans
  refine ⟨q00100, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00100, r00100, r00000, r00001, r00003, r00004, r00025, r00032, r00058, r00090, r00099, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00101 : UPoly := (Polynomial.C ((131520519178494644166728 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-255911675856993440149676618 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-9703129255263301208106512 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-465378990293510591951780 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2377231995197870783002508 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1710265169925696767398648 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q00101 : UPoly := (Polynomial.C ((-6154588013304852523894 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-595968515756076931573936 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-33568121086637785522568 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-222270371631318645500 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-31422673771881626808 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-381441438531089496 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-1226900085860736 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-195035156333363808 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-1193703430062528 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-317579693760 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((-492883684715520 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((-317579693760 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((-127031877504 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 13)
lemma mod_a00101 : Modulo (spec a00101) r00101 := by
  have h : Modulo (spec a00101) ((Polynomial.C ((-27 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00009 ^ 1 * r00012 ^ 5 * r00014 ^ 4 * r00035 ^ 1) + (Polynomial.C ((-1 : ℂ) / (2 : ℂ)) * r00001 ^ 5 * r00002 ^ 3 * r00004 ^ 1 * r00005 ^ 3 * r00012 ^ 3 * r00014 ^ 2 * r00046 ^ 1) + (Polynomial.C ((-1 : ℂ) / (1152 : ℂ)) * r00000 ^ 1 * r00001 ^ 13 * r00002 ^ 6 * r00004 ^ 5 * r00005 ^ 5 * r00012 ^ 1 * r00082 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 1 * r00004 ^ 1 * r00005 ^ 2 * r00012 ^ 4 * r00014 ^ 3 * r00039 ^ 1) + (Polynomial.C ((1 : ℂ) / (8 : ℂ)) * r00000 ^ 1 * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00012 ^ 2 * r00014 ^ 1 * r00061 ^ 1) + (Polynomial.C ((1 : ℂ) / (5760 : ℂ)) * r00000 ^ 1 * r00001 ^ 18 * r00002 ^ 6 * r00004 ^ 6 * r00005 ^ 6 * r00014 ^ 1 * r00100 ^ 1)) := by
    unfold a00101
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((((Modulo.refl (Polynomial.C ((-27 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00012.pow 5)).mul (mod_a00014.pow 4)).mul (mod_a00035.pow 1)).add ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (2 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 3)).mul (mod_a00012.pow 3)).mul (mod_a00014.pow 2)).mul (mod_a00046.pow 1))).add ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1152 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 13)).mul (mod_a00002.pow 6)).mul (mod_a00004.pow 5)).mul (mod_a00005.pow 5)).mul (mod_a00012.pow 1)).mul (mod_a00082.pow 1))).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 2)).mul (mod_a00012.pow 4)).mul (mod_a00014.pow 3)).mul (mod_a00039.pow 1))).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (8 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00012.pow 2)).mul (mod_a00014.pow 1)).mul (mod_a00061.pow 1))).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (5760 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 18)).mul (mod_a00002.pow 6)).mul (mod_a00004.pow 6)).mul (mod_a00005.pow 6)).mul (mod_a00014.pow 1)).mul (mod_a00100.pow 1)))
  apply h.trans
  refine ⟨q00101, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00101, r00101, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00012, r00014, r00035, r00039, r00046, r00061, r00082, r00100, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00102 : UPoly := (Polynomial.C ((-13502792 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0)
def q00102 : UPoly := 0
lemma mod_a00102 : Modulo (spec a00102) r00102 := by
  have h : Modulo (spec a00102) ((Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00006 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1 * r00012 ^ 3) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00012 ^ 1)) := by
    unfold a00102
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00006.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).mul (mod_a00012.pow 3))).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00012.pow 1)))
  apply h.trans
  refine ⟨q00102, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00102, r00102, r00001, r00002, r00004, r00005, r00006, r00007, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00103 : UPoly := (Polynomial.C ((-877555282166824 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-40521586205342 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-209156977936 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-81945240112588 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-869178133408 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2431783928 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q00103 : UPoly := (Polynomial.C ((-851648727586 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-4873855472 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-3528 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2916607168 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2571928 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-32 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00103 : Modulo (spec a00103) r00103 := by
  have h : Modulo (spec a00103) ((Polynomial.C ((-1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00012 ^ 2 * r00014 ^ 2) + (Polynomial.C ((-1 : ℂ) / (46656 : ℂ)) * r00000 ^ 9 * r00001 ^ 12 * r00002 ^ 3 * r00003 ^ 3 * r00004 ^ 6 * r00005 ^ 3 * r00017 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 3 * r00102 ^ 1)) := by
    unfold a00103
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00012.pow 2)).mul (mod_a00014.pow 2)).add ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (46656 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 12)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 6)).mul (mod_a00005.pow 3)).mul (mod_a00017.pow 1))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 3)).mul (mod_a00102.pow 1)))
  apply h.trans
  refine ⟨q00103, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00103, r00103, r00000, r00001, r00002, r00003, r00004, r00005, r00012, r00014, r00017, r00102, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00104 : UPoly := (Polynomial.C ((1353397072 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((41579240 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((35369 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((83158472 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((15876 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1280 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00104 : UPoly := (Polynomial.C ((428656 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((8 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00104 : Modulo (spec a00104) r00104 := by
  have h : Modulo (spec a00104) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 1 * r00012 ^ 2 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (108 : ℂ)) * r00000 ^ 5 * r00001 ^ 8 * r00003 ^ 1 * r00004 ^ 4 * r00005 ^ 1 * r00014 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 5 * r00001 ^ 8 * r00003 ^ 1 * r00004 ^ 4 * r00005 ^ 1 * r00009 ^ 1)) := by
    unfold a00104
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 1)).mul (mod_a00012.pow 2)).mul (mod_a00014.pow 2)).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (108 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 8)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 1))).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 8)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)))
  apply h.trans
  refine ⟨q00104, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00104, r00104, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00012, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00105 : UPoly := (Polynomial.C ((10381590242422559552 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-705297244415684624 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-15813421471340608 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((1322807049694677152 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-21448811881867982 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-35470073329504 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00105 : UPoly := (Polynomial.C ((13829808285601808 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((142584718073216 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((793256450848 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((3010560 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((3276800 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a00105 : Modulo (spec a00105) r00105 := by
  have h : Modulo (spec a00105) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00001 ^ 4 * r00004 ^ 2 * r00025 ^ 1 * r00103 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 3 * r00003 ^ 1 * r00005 ^ 1 * r00104 ^ 2)) := by
    unfold a00105
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 4)).mul (mod_a00004.pow 2)).mul (mod_a00025.pow 1)).mul (mod_a00103.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00104.pow 2)))
  apply h.trans
  refine ⟨q00105, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00105, r00105, r00000, r00001, r00002, r00003, r00004, r00005, r00025, r00103, r00104, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00106 : UPoly := (Polynomial.C ((-214327 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0)
def q00106 : UPoly := 0
lemma mod_a00106 : Modulo (spec a00106) r00106 := by
  have h : Modulo (spec a00106) ((Polynomial.C ((-3 : ℂ) / (1 : ℂ)) * r00005 ^ 6 * r00012 ^ 2) + (Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 6 * r00012 ^ 2)) := by
    unfold a00106
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((-3 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)).mul (mod_a00012.pow 2)).add (((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 6)).mul (mod_a00012.pow 2)))
  apply h.trans
  refine ⟨q00106, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00106, r00106, r00001, r00002, r00004, r00005, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00118 : UPoly := (Polynomial.C ((-589530603061655981696 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-46637956727735323408 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-87826730585985668 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-146953633814659750336 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2575338693496677632 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-10824838443833522 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q00118 : UPoly := (Polynomial.C ((-3586279995763606304 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-43562833741424756 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-233768453688640 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-27662468815397696 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-285171979496192 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1586516178496 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-6021120 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-6553600 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a00118 : Modulo (spec a00118) r00118 := by
  have h : Modulo (spec a00118) ((Polynomial.C ((-1 : ℂ) / (288 : ℂ)) * r00000 ^ 5 * r00001 ^ 8 * r00002 ^ 3 * r00003 ^ 2 * r00004 ^ 4 * r00005 ^ 2 * r00025 ^ 2 * r00104 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 3 * r00003 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00104 ^ 2) + (Polynomial.C ((1 : ℂ) / (4 : ℂ)) * r00000 ^ 1 * r00001 ^ 4 * r00004 ^ 2 * r00009 ^ 1 * r00025 ^ 1 * r00103 ^ 1)) := by
    unfold a00118
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (288 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 8)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00025.pow 2)).mul (mod_a00104.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00104.pow 2))).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (4 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 4)).mul (mod_a00004.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00103.pow 1)))
  apply h.trans
  refine ⟨q00118, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00118, r00118, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00025, r00103, r00104, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00119 : UPoly := (Polynomial.C ((191 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q00119 : UPoly := 0
lemma mod_a00119 : Modulo (spec a00119) r00119 := by
  have h : Modulo (spec a00119) ((Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * r00012 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1)) := by
    unfold a00119
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-2 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)))
  apply h.trans
  refine ⟨q00119, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00119, r00119, r00006, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00120 : UPoly := (Polynomial.C ((24808662512 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-42759831596 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-553021216 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((2314663874 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((15599415392 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((162949612 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00120 : UPoly := (Polynomial.C ((24497324 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((332757592 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((63504 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((90704 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1714640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((64 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00120 : Modulo (spec a00120) r00120 := by
  have h : Modulo (spec a00120) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 4 * r00002 ^ 1 * r00003 ^ 2 * r00012 ^ 2 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00014 ^ 3 * r00119 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 8 * r00003 ^ 3 * r00004 ^ 4 * r00005 ^ 1 * r00017 ^ 1)) := by
    unfold a00120
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a00012.pow 2)).mul (mod_a00014.pow 2)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 3)).mul (mod_a00119.pow 1))).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 8)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 1)).mul (mod_a00017.pow 1)))
  apply h.trans
  refine ⟨q00120, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00120, r00120, r00000, r00001, r00002, r00003, r00004, r00005, r00012, r00014, r00017, r00119, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00121 : UPoly := (Polynomial.C ((52462469892590048 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((4991967651641056 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((17442713301322 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((10510026284044064 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((24401404949704 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1453551076288 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q00121 : UPoly := (Polynomial.C ((6070108833968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1759644835648 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4973302768 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((327680 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00121 : Modulo (spec a00121) r00121 := by
  have h : Modulo (spec a00121) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00103 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00025 ^ 1 * r00104 ^ 1)) := by
    unfold a00121
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00103.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00025.pow 1)).mul (mod_a00104.pow 1)))
  apply h.trans
  refine ⟨q00121, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00121, r00121, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00025, r00103, r00104, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00122 : UPoly := (Polynomial.C ((-84712999040 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-6608097184 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-47599292 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-4480875209 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-64583560 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-262774 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q00122 : UPoly := (Polynomial.C ((-55439408 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-31752 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2560 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a00122 : Modulo (spec a00122) r00122 := by
  have h : Modulo (spec a00122) ((Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00000 ^ 5 * r00001 ^ 8 * r00003 ^ 1 * r00004 ^ 4 * r00005 ^ 1 * r00025 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r00104 ^ 1)) := by
    unfold a00122
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 8)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 1)).mul (mod_a00025.pow 2)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a00104.pow 1)))
  apply h.trans
  refine ⟨q00122, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00122, r00122, r00000, r00001, r00003, r00004, r00005, r00009, r00025, r00104, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00123 : UPoly := (Polynomial.C ((314449734828682993704085413856 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-105052254409219267639958527492504 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-5328817447003068297325101269200 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-111559817459929275627085874972 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-40994647210470989804034774159680 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1570728402329484327701282517160 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00123 : UPoly := (Polynomial.C ((-2069017075800509651087156112440 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-222816296615476892462468570979616 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-6716547528548091115225871035876 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-75869234187773549015742848960 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-34044520601844558684081592 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((7439077021155580979224189696 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((72297011897203993057798592 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((2537334531445150792081408 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((35264222639742273933329408 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((881988728960520365625344 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((2834065167244913941760 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((4111473899191226368 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((20448306876680704 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a00123 : Modulo (spec a00123) r00123 := by
  have h : Modulo (spec a00123) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 5 * r00001 ^ 4 * r00002 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00032 ^ 1 * r00103 ^ 1 * r00122 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 3 * r00005 ^ 2 * r00118 ^ 1 * r00120 ^ 1) + (Polynomial.C ((54 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00025 ^ 1 * r00103 ^ 1 * r00121 ^ 1)) := by
    unfold a00123
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00032.pow 1)).mul (mod_a00103.pow 1)).mul (mod_a00122.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 3)).mul (mod_a00005.pow 2)).mul (mod_a00118.pow 1)).mul (mod_a00120.pow 1))).add (((((Modulo.refl (Polynomial.C ((54 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a00103.pow 1)).mul (mod_a00121.pow 1)))
  apply h.trans
  refine ⟨q00123, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00123, r00123, r00000, r00001, r00002, r00003, r00004, r00005, r00025, r00032, r00103, r00118, r00120, r00121, r00122, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00124 : UPoly := (Polynomial.C ((6737287312019321440 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((645588239240646344 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((181064122530736 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((1287946956436912708 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((20620119118263452 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((2648103080 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q00124 : UPoly := (Polynomial.C ((19326504384826936 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5293094464 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-259308 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((432089344 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a00124 : Modulo (spec a00124) r00124 := by
  have h : Modulo (spec a00124) ((Polynomial.C ((-1 : ℂ) / (11664 : ℂ)) * r00000 ^ 9 * r00001 ^ 12 * r00002 ^ 3 * r00003 ^ 3 * r00004 ^ 6 * r00005 ^ 3 * r00102 ^ 1) + (Polynomial.C ((-1 : ℂ) / (15552 : ℂ)) * r00000 ^ 8 * r00001 ^ 8 * r00002 ^ 8 * r00003 ^ 4 * r00004 ^ 4 * r00005 ^ 4 * r00012 ^ 4) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 2 * r00102 ^ 2) + (Polynomial.C ((1 : ℂ) / (36 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00009 ^ 1 * r00012 ^ 2 * r00102 ^ 1) + (Polynomial.C ((1 : ℂ) / (54 : ℂ)) * r00000 ^ 3 * r00002 ^ 9 * r00003 ^ 3 * r00005 ^ 3 * r00009 ^ 1 * r00012 ^ 6)) := by
    unfold a00124
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (11664 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 12)).mul (mod_a00002.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 6)).mul (mod_a00005.pow 3)).mul (mod_a00102.pow 1)).add ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (15552 : ℂ)))).mul (mod_a00000.pow 8)).mul (mod_a00001.pow 8)).mul (mod_a00002.pow 8)).mul (mod_a00003.pow 4)).mul (mod_a00004.pow 4)).mul (mod_a00005.pow 4)).mul (mod_a00012.pow 4))).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 2)).mul (mod_a00102.pow 2))).add ((((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (36 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00012.pow 2)).mul (mod_a00102.pow 1))).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (54 : ℂ)))).mul (mod_a00000.pow 3)).mul (mod_a00002.pow 9)).mul (mod_a00003.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00009.pow 1)).mul (mod_a00012.pow 6)))
  apply h.trans
  refine ⟨q00124, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00124, r00124, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00012, r00102, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00126 : UPoly := (Polynomial.C ((540660620960 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((25005141496 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((43123264 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((50527677248 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((57980416 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1351840 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q00126 : UPoly := (Polynomial.C ((110744 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((24704 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-814976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1696 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-10304 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-32 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 9)
lemma mod_a00126 : Modulo (spec a00126) r00126 := by
  have h : Modulo (spec a00126) ((Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00032 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00025 ^ 1 * r00042 ^ 1)) := by
    unfold a00126
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00032.pow 2)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00025.pow 1)).mul (mod_a00042.pow 1)))
  apply h.trans
  refine ⟨q00126, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00126, r00126, r00000, r00001, r00003, r00004, r00025, r00032, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00128 : UPoly := (Polynomial.C ((1032 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00128 : UPoly := 0
lemma mod_a00128 : Modulo (spec a00128) r00128 := by
  have h : Modulo (spec a00128) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00017 ^ 1) + (Polynomial.C ((8 : ℂ) / (1 : ℂ)) * r00003 ^ 6)) := by
    unfold a00128
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00017.pow 1)).add ((Modulo.refl (Polynomial.C ((8 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)))
  apply h.trans
  refine ⟨q00128, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00128, r00128, r00003, r00017, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00129 : UPoly := (Polynomial.C ((532004192 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((16344376 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((42124 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((32620112 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((55948 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00129 : UPoly := (Polynomial.C ((167192 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-4 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((512 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((2 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 6)
lemma mod_a00129 : Modulo (spec a00129) r00129 := by
  have h : Modulo (spec a00129) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 3 * r00006 ^ 1 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (1296 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00004 ^ 3 * r00128 ^ 1)) := by
    unfold a00129
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 3)).mul (mod_a00006.pow 1)).mul (mod_a00014.pow 2)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1296 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00128.pow 1)))
  apply h.trans
  refine ⟨q00129, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00129, r00129, r00000, r00001, r00003, r00004, r00006, r00014, r00128, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00130 : UPoly := (Polynomial.C ((224 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0)
def q00130 : UPoly := 0
lemma mod_a00130 : Modulo (spec a00130) r00130 := by
  have h : Modulo (spec a00130) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 6) + (Polynomial.C ((1 : ℂ) / (12 : ℂ)) * r00025 ^ 1)) := by
    unfold a00130
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (12 : ℂ)))).mul (mod_a00025.pow 1)))
  apply h.trans
  refine ⟨q00130, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00130, r00130, r00003, r00025, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00131 : UPoly := (Polynomial.C ((124 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00131 : UPoly := 0
lemma mod_a00131 : Modulo (spec a00131) r00131 := by
  have h : Modulo (spec a00131) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1) + (Polynomial.C ((3 : ℂ) / (1 : ℂ)) * r00003 ^ 6)) := by
    unfold a00131
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).add ((Modulo.refl (Polynomial.C ((3 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)))
  apply h.trans
  refine ⟨q00131, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00131, r00131, r00003, r00009, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00132 : UPoly := (Polynomial.C ((388 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00132 : UPoly := 0
lemma mod_a00132 : Modulo (spec a00132) r00132 := by
  have h : Modulo (spec a00132) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 1) + (Polynomial.C ((3 : ℂ) / (1 : ℂ)) * r00003 ^ 6)) := by
    unfold a00132
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 1)).add ((Modulo.refl (Polynomial.C ((3 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 6)))
  apply h.trans
  refine ⟨q00132, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00132, r00132, r00003, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00133 : UPoly := (Polynomial.C ((900 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
def q00133 : UPoly := 0
lemma mod_a00133 : Modulo (spec a00133) r00133 := by
  have h : Modulo (spec a00133) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00131 ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * r00132 ^ 1)) := by
    unfold a00133
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00131.pow 1)).add ((Modulo.refl (Polynomial.C ((2 : ℂ) / (1 : ℂ)))).mul (mod_a00132.pow 1)))
  apply h.trans
  refine ⟨q00133, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00133, r00133, r00131, r00132, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r00134 : UPoly := (Polynomial.C ((54362683381616244843520 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((6841061300379958346240 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((124395021160018481600 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((16931601259248741578240 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((598209514760583714560 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((8833943371037024240 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
def q00134 : UPoly := (Polynomial.C ((363916566136729113856 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((95601052202779288640 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((3352811439524220160 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-5493940565679572800 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-152320283324543056 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-575360575781632 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-360304671461362016 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-2638490527339520 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-67522831688384 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-1725087325717648 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((-89005444078720 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((-551735870272 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((-3261347777792 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 12) + (Polynomial.C ((-50460694208 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 13) + (Polynomial.C ((-781470208 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 14) + (Polynomial.C ((-1345792 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 15)
lemma mod_a00134 : Modulo (spec a00134) r00134 := by
  have h : Modulo (spec a00134) ((Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * r00042 ^ 1 * r00054 ^ 1 * r00130 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00003 ^ 3 * r00064 ^ 1 * r00129 ^ 1) + (Polynomial.C ((1 : ℂ) / (324 : ℂ)) * r00000 ^ 9 * r00001 ^ 3 * r00003 ^ 3 * r00004 ^ 3 * r00042 ^ 1 * r00058 ^ 1 * r00133 ^ 1) + (Polynomial.C ((2 : ℂ) / (3 : ℂ)) * r00003 ^ 6 * r00042 ^ 1 * r00126 ^ 1)) := by
    unfold a00134
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-2 : ℂ) / (1 : ℂ)))).mul (mod_a00042.pow 1)).mul (mod_a00054.pow 1)).mul (mod_a00130.pow 1)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00003.pow 3)).mul (mod_a00064.pow 1)).mul (mod_a00129.pow 1))).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (324 : ℂ)))).mul (mod_a00000.pow 9)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00042.pow 1)).mul (mod_a00058.pow 1)).mul (mod_a00133.pow 1))).add ((((Modulo.refl (Polynomial.C ((2 : ℂ) / (3 : ℂ)))).mul (mod_a00003.pow 6)).mul (mod_a00042.pow 1)).mul (mod_a00126.pow 1)))
  apply h.trans
  refine ⟨q00134, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q00134, r00134, r00000, r00001, r00003, r00004, r00042, r00054, r00058, r00064, r00126, r00129, r00130, r00133, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r01732 : UPoly := (Polynomial.C ((214327 : ℂ) / (54 : ℂ)) * Polynomial.X ^ 0)
def q01732 : UPoly := 0
lemma mod_a01732 : Modulo (spec a01732) r01732 := by
  have h : Modulo (spec a01732) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00005 ^ 3 * r00012 ^ 2) + (Polynomial.C ((1 : ℂ) / (432 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3)) := by
    unfold a01732
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 3)).mul (mod_a00012.pow 2)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (432 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)))
  apply h.trans
  refine ⟨q01732, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q01732, r01732, r00001, r00002, r00004, r00005, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07824 : UPoly := (Polynomial.C ((1462476088 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((29625934 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2036192 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((136463972 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6685033 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((36376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07824 : UPoly := (Polynomial.C ((738224 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((13088 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((16 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((5120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a07824 : Modulo (spec a07824) r07824 := by
  have h : Modulo (spec a07824) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00018 ^ 1) + (Polynomial.C ((1 : ℂ) / (6 : ℂ)) * r00000 ^ 1 * r00003 ^ 1 * r00015 ^ 1 * r00019 ^ 1)) := by
    unfold a07824
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00018.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (6 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00003.pow 1)).mul (mod_a00015.pow 1)).mul (mod_a00019.pow 1)))
  apply h.trans
  refine ⟨q07824, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07824, r07824, r00000, r00003, r00015, r00018, r00019, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07865 : UPoly := (Polynomial.C ((21004046 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((214327 : ℂ) / (54 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((214327 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((7 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4)
def q07865 : UPoly := 0
lemma mod_a07865 : Modulo (spec a07865) r07865 := by
  have h : Modulo (spec a07865) ((Polynomial.C ((-1 : ℂ) / (432 : ℂ)) * r00000 ^ 4 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00012 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00005 ^ 1 * r00014 ^ 1 * r01732 ^ 1)) := by
    unfold a07865
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (432 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00012.pow 1)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 1)).mul (mod_a00014.pow 1)).mul (mod_a01732.pow 1)))
  apply h.trans
  refine ⟨q07865, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07865, r07865, r00000, r00001, r00002, r00003, r00004, r00005, r00012, r00014, r01732, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07866 : UPoly := (Polynomial.C ((-1832807393299681325145441412 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-113481690363005994073248227 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((813478172529733181753608 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1701238252051175365033545182 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-863700190836543633716597 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((149977031752432410797780 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 5)
def q07866 : UPoly := (Polynomial.C ((3205826899822544646093385 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((306956964836776698144016 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((5887017016975215924898 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((3971458250409528802 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((2236533564636952 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a07866 : Modulo (spec a07866) r07866 := by
  have h : Modulo (spec a07866) ((Polynomial.C ((-1 : ℂ) / (4 : ℂ)) * r00002 ^ 4 * r00003 ^ 1 * r00012 ^ 1 * r00103 ^ 1 * r00122 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00005 ^ 1 * r00118 ^ 1 * r07865 ^ 1)) := by
    unfold a07866
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (4 : ℂ)))).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 1)).mul (mod_a00012.pow 1)).mul (mod_a00103.pow 1)).mul (mod_a00122.pow 1)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 1)).mul (mod_a00118.pow 1)).mul (mod_a07865.pow 1)))
  apply h.trans
  refine ⟨q07866, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07866, r07866, r00002, r00003, r00005, r00012, r00103, r00118, r00122, r07865, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07867 : UPoly := (Polynomial.C ((-623074088778116142805597679372352 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-35878009457054348702300486878224 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-836844621996098981832190955520 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-103189410090719903286028376180448 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-4546483826904765733104183607296 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-83901388595212475313608011584 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07867 : UPoly := (Polynomial.C ((-5749741994973996098219645453872 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-108942108442994952409853341696 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((3680800939188535290097547200 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-254029182402900491271663612032 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-386937685494771547905035456 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((67189710225089720037405440 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5)
lemma mod_a07867 : Modulo (spec a07867) r07867 := by
  have h : Modulo (spec a07867) ((Polynomial.C ((-432 : ℂ) / (1 : ℂ)) * r00005 ^ 1 * r00012 ^ 1 * r00014 ^ 2 * r07866 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 4 * r00004 ^ 2 * r00123 ^ 1)) := by
    unfold a07867
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((-432 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 1)).mul (mod_a00012.pow 1)).mul (mod_a00014.pow 2)).mul (mod_a07866.pow 1)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 4)).mul (mod_a00004.pow 2)).mul (mod_a00123.pow 1)))
  apply h.trans
  refine ⟨q07867, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07867, r07867, r00001, r00004, r00005, r00012, r00014, r00123, r07866, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07868 : UPoly := (Polynomial.C ((-2 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q07868 : UPoly := 0
lemma mod_a07868 : Modulo (spec a07868) r07868 := by
  have h : Modulo (spec a07868) ((Polynomial.C ((-3 : ℂ) / (1 : ℂ)) * r00005 ^ 6) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 6)) := by
    unfold a07868
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-3 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 6)))
  apply h.trans
  refine ⟨q07868, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07868, r07868, r00002, r00005, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07869 : UPoly := (Polynomial.C ((38592 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1180 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1409 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((2392 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4096 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q07869 : UPoly := (Polynomial.C ((-4 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-32 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07869 : Modulo (spec a07869) r07869 := by
  have h : Modulo (spec a07869) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00014 ^ 2) + (Polynomial.C ((1 : ℂ) / (3 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00017 ^ 1 * r07868 ^ 1)) := by
    unfold a07869
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (3 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00017.pow 1)).mul (mod_a07868.pow 1)))
  apply h.trans
  refine ⟨q07869, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07869, r07869, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00017, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07870 : UPoly := (Polynomial.C ((-8449878152 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-391417606 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2029712 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-787907546 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-7913024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-18748 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07870 : UPoly := (Polynomial.C ((-8174522 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-37336 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-36272 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a07870 : Modulo (spec a07870) r07870 := by
  have h : Modulo (spec a07870) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1 * r00014 ^ 3 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (72 : ℂ)) * r00000 ^ 4 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r07869 ^ 1)) := by
    unfold a07870
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)).mul (mod_a00014.pow 3)).mul (mod_a07868.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (72 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a07869.pow 1)))
  apply h.trans
  refine ⟨q07870, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07870, r07870, r00000, r00001, r00003, r00004, r00006, r00014, r07868, r07869, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07871 : UPoly := (Polynomial.C ((38944 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((396 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2113 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((808 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2560 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07871 : UPoly := (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-16 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07871 : Modulo (spec a07871) r07871 := by
  have h : Modulo (spec a07871) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00032 ^ 1 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00014 ^ 2)) := by
    unfold a07871
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00032.pow 1)).mul (mod_a07868.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)))
  apply h.trans
  refine ⟨q07871, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07871, r07871, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00032, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07873 : UPoly := (Polynomial.C ((-4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q07873 : UPoly := 0
lemma mod_a07873 : Modulo (spec a07873) r07873 := by
  have h : Modulo (spec a07873) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00007 ^ 1) + (Polynomial.C ((3 : ℂ) / (1 : ℂ)) * r07868 ^ 1)) := by
    unfold a07873
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00007.pow 1)).add ((Modulo.refl (Polynomial.C ((3 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)))
  apply h.trans
  refine ⟨q07873, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07873, r07873, r00007, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07889 : UPoly := (Polynomial.C ((16 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
def q07889 : UPoly := 0
lemma mod_a07889 : Modulo (spec a07889) r07889 := by
  have h : Modulo (spec a07889) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07868 ^ 1) + (Polynomial.C ((18 : ℂ) / (1 : ℂ)) * r00005 ^ 6)) := by
    unfold a07889
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)).add ((Modulo.refl (Polynomial.C ((18 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)))
  apply h.trans
  refine ⟨q07889, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07889, r07889, r00005, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07895 : UPoly := 0
def q07895 : UPoly := 0
lemma mod_a07895 : Modulo (spec a07895) r07895 := by
  have h : Modulo (spec a07895) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07868 ^ 1) + (Polynomial.C ((2 : ℂ) / (1 : ℂ)) * r00005 ^ 6)) := by
    unfold a07895
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)).add ((Modulo.refl (Polynomial.C ((2 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)))
  apply h.trans
  refine ⟨q07895, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07895, r07895, r00005, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07914 : UPoly := (Polynomial.C ((-41529086617164999904 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-3906101398013343688 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-154316045901215192 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-77410851535910319280 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1986066812361366640 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-20318105540708192 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q07914 : UPoly := (Polynomial.C ((-413884100181928552 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24938320426052672 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-184312820716576 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-82984352000 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((7154944288 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((498176 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((146184704 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((1498112 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((1280 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((600064 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((1024 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((1024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a07914 : Modulo (spec a07914) r07914 := by
  have h : Modulo (spec a07914) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07868 ^ 1 * r07870 ^ 2) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00014 ^ 6 * r07873 ^ 2)) := by
    unfold a07914
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)).mul (mod_a07870.pow 2)).add (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00014.pow 6)).mul (mod_a07873.pow 2)))
  apply h.trans
  refine ⟨q07914, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07914, r07914, r00001, r00002, r00004, r00005, r00014, r07868, r07870, r07873, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07915 : UPoly := (Polynomial.C ((-214325 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0)
def q07915 : UPoly := 0
lemma mod_a07915 : Modulo (spec a07915) r07915 := by
  have h : Modulo (spec a07915) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00012 ^ 2 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3)) := by
    unfold a07915
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 2)).mul (mod_a07868.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)))
  apply h.trans
  refine ⟨q07915, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07915, r07915, r00001, r00002, r00004, r00005, r00012, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07916 : UPoly := (Polynomial.C ((-642977 : ℂ) / (54 : ℂ)) * Polynomial.X ^ 0)
def q07916 : UPoly := 0
lemma mod_a07916 : Modulo (spec a07916) r07916 := by
  have h : Modulo (spec a07916) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00012 ^ 2 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r07915 ^ 1)) := by
    unfold a07916
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 2)).mul (mod_a07868.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a07915.pow 1)))
  apply h.trans
  refine ⟨q07916, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07916, r07916, r00012, r07868, r07915, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07917 : UPoly := (Polynomial.C ((-71441 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0)
def q07917 : UPoly := 0
lemma mod_a07917 : Modulo (spec a07917) r07917 := by
  have h : Modulo (spec a07917) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07915 ^ 1) + (Polynomial.C ((1 : ℂ) / (108 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3)) := by
    unfold a07917
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07915.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (108 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)))
  apply h.trans
  refine ⟨q07917, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07917, r07917, r00001, r00002, r00004, r00005, r07915, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07918 : UPoly := (Polynomial.C ((-3896859028756013032009424 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-363038996773229169577484 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-14186725239283080394516 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-7292959107923568768133256 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-191059694980886392378520 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2019052297159275378448 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 5)
def q07918 : UPoly := (Polynomial.C ((-945474315373578545296 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-19303829847684419968 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-16330862707763968 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-8175279983853473792 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-41435432446964864 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-206688373520384 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-25218328601799424 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-253260827717632 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-600040388864 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 8)
lemma mod_a07918 : Modulo (spec a07918) r07918 := by
  have h : Modulo (spec a07918) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00012 ^ 1 * r00014 ^ 3 * r07868 ^ 1 * r07870 ^ 1 * r07873 ^ 1 * r07917 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07914 ^ 1 * r07916 ^ 1)) := by
    unfold a07918
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 1)).mul (mod_a00014.pow 3)).mul (mod_a07868.pow 1)).mul (mod_a07870.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07917.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07914.pow 1)).mul (mod_a07916.pow 1)))
  apply h.trans
  refine ⟨q07918, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07918, r07918, r00012, r00014, r07868, r07870, r07873, r07914, r07916, r07917, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07919 : UPoly := (Polynomial.C ((8028871552 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-12966245212448 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-197466894016 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-723691040 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-406655863036 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4828489152 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07919 : UPoly := (Polynomial.C ((-14866144 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-95677184 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-16547776 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-81920 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((26214400 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a07919 : Modulo (spec a07919) r07919 := by
  have h : Modulo (spec a07919) ((Polynomial.C ((-54 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00025 ^ 1 * r07868 ^ 1 * r07870 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 3 * r00003 ^ 1 * r00004 ^ 1 * r07871 ^ 2)) := by
    unfold a07919
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((-54 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a07868.pow 1)).mul (mod_a07870.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a07871.pow 2)))
  apply h.trans
  refine ⟨q07919, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07919, r07919, r00000, r00001, r00003, r00004, r00025, r07868, r07870, r07871, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07920 : UPoly := (Polynomial.C ((-1394517218816 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((773957643959072 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((24261178166312 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((207580948672 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((52086375065440 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1126297556604 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07920 : UPoly := (Polynomial.C ((6428439040 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((816155857400 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((9974696832 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((1572864 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1006632960 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a07920 : Modulo (spec a07920) r07920 := by
  have h : Modulo (spec a07920) ((Polynomial.C ((-3 : ℂ) / (4 : ℂ)) * r00000 ^ 5 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00025 ^ 2 * r07868 ^ 1 * r07871 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r07919 ^ 1)) := by
    unfold a07920
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-3 : ℂ) / (4 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00025.pow 2)).mul (mod_a07868.pow 1)).mul (mod_a07871.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a07919.pow 1)))
  apply h.trans
  refine ⟨q07920, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07920, r07920, r00000, r00001, r00003, r00004, r00009, r00025, r07868, r07871, r07919, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07921 : UPoly := (Polynomial.C ((40000 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((404 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((4225 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((840 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4096 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07921 : UPoly := (Polynomial.C ((-12 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-32 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07921 : Modulo (spec a07921) r07921 := by
  have h : Modulo (spec a07921) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00017 ^ 1 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 1 * r00002 ^ 4 * r00005 ^ 2 * r00014 ^ 2)) := by
    unfold a07921
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00017.pow 1)).mul (mod_a07868.pow 1)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 1)).mul (mod_a00002.pow 4)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)))
  apply h.trans
  refine ⟨q07921, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07921, r07921, r00000, r00001, r00002, r00003, r00004, r00005, r00014, r00017, r07868, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07922 : UPoly := (Polynomial.C ((-2816625992 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-130335958 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-224944 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-787907522 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-8058368 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-2252 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5)
def q07922 : UPoly := (Polynomial.C ((-2724842 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-13480 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-36272 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a07922 : Modulo (spec a07922) r07922 := by
  have h : Modulo (spec a07922) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00006 ^ 1 * r00014 ^ 3 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00000 ^ 4 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r07921 ^ 1)) := by
    unfold a07922
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00006.pow 1)).mul (mod_a00014.pow 3)).mul (mod_a07868.pow 1)).add ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a07921.pow 1)))
  apply h.trans
  refine ⟨q07922, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07922, r07922, r00000, r00001, r00003, r00004, r00006, r00014, r07868, r07921, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07923 : UPoly := (Polynomial.C ((17132289345674686202080 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-4733361997666435326284888 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-704032129391745522037088 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-398930455225320906424 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1848163876203736029168640 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-71654637106702656602032 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07923 : UPoly := (Polynomial.C ((-100033756824742341944 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-41042310858950134270528 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1307113129967947206392 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-375234244902808960 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((179854391199504 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((24235597824000 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((211257999360 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((12224414875648 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((212511850496 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((1215561728 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((85293465600 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((974127104 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((2752512 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 12) + (Polynomial.C ((325058560 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 13) + (Polynomial.C ((1835008 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 14) + (Polynomial.C ((524288 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 16)
lemma mod_a07923 : Modulo (spec a07923) r07923 := by
  have h : Modulo (spec a07923) ((Polynomial.C ((-1 : ℂ) / (2 : ℂ)) * r00000 ^ 1 * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00009 ^ 1 * r00014 ^ 6 * r00025 ^ 1 * r07868 ^ 1 * r07873 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07920 ^ 1 * r07922 ^ 1)) := by
    unfold a07923
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 6)).mul (mod_a00025.pow 1)).mul (mod_a07868.pow 1)).mul (mod_a07873.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07920.pow 1)).mul (mod_a07922.pow 1)))
  apply h.trans
  refine ⟨q07923, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07923, r07923, r00000, r00001, r00002, r00004, r00005, r00009, r00014, r00025, r07868, r07873, r07920, r07922, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07924 : UPoly := (Polynomial.C ((168445499296 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5370035008 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((509004518 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((101044503376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((76554258 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((4357664 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q07924 : UPoly := (Polynomial.C ((1573982192 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5206400 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((36472 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((655360 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a07924 : Modulo (spec a07924) r07924 := by
  have h : Modulo (spec a07924) ((Polynomial.C ((-1 : ℂ) / (216 : ℂ)) * r00000 ^ 4 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00025 ^ 1 * r07871 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r07870 ^ 1)) := by
    unfold a07924
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (216 : ℂ)))).mul (mod_a00000.pow 4)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00025.pow 1)).mul (mod_a07871.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a07870.pow 1)))
  apply h.trans
  refine ⟨q07924, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07924, r07924, r00000, r00001, r00003, r00004, r00009, r00025, r07870, r07871, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07925 : UPoly := (Polynomial.C ((6204209564348176054144 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((945584298245787521152 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((57400233292864591432 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((7193696094501369993032 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((91443681454831921216 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((4200608069659776896 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q07925 : UPoly := (Polynomial.C ((53083387557860037856 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((4856202437529761240 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((57099385860444416 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((58752203358224 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-688637766656 : ℂ) / (243 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-91691840 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-47751620608 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-830124416 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-4748288 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-111059200 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((-3805184 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((-3584 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((-1269760 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 12) + (Polynomial.C ((-7168 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 13) + (Polynomial.C ((-2048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 15)
lemma mod_a07925 : Modulo (spec a07925) r07925 := by
  have h : Modulo (spec a07925) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07868 ^ 1 * r07870 ^ 1 * r07924 ^ 1) + (Polynomial.C ((1 : ℂ) / (216 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00009 ^ 1 * r00014 ^ 6 * r07873 ^ 2)) := by
    unfold a07925
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)).mul (mod_a07870.pow 1)).mul (mod_a07924.pow 1)).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (216 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 6)).mul (mod_a07873.pow 2)))
  apply h.trans
  refine ⟨q07925, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07925, r07925, r00001, r00002, r00004, r00005, r00009, r00014, r07868, r07870, r07873, r07924, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07926 : UPoly := (Polynomial.C ((4081218740376331649696 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((93337487593058747007736 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((22176611661019294207648 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((196958455580429462488 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-6577676011385310952448 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-1425889749391741108144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07926 : UPoly := (Polynomial.C ((1075355665832902885376 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a07926 : Modulo (spec a07926) r07926 := by
  have h : Modulo (spec a07926) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07923 ^ 1) + (Polynomial.C ((54 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00025 ^ 1 * r07925 ^ 1)) := by
    unfold a07926
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07923.pow 1)).add ((((Modulo.refl (Polynomial.C ((54 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a07925.pow 1)))
  apply h.trans
  refine ⟨q07926, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07926, r07926, r00000, r00025, r07923, r07925, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07927 : UPoly := (Polynomial.C ((-2772800 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-65760 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-819912 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-141953 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1856 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((290682 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07927 : UPoly := (Polynomial.C ((944 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((5120 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07927 : Modulo (spec a07927) r07927 := by
  have h : Modulo (spec a07927) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00000 ^ 5 * r00003 ^ 1 * r00004 ^ 1 * r00025 ^ 2 * r07868 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r07871 ^ 1)) := by
    unfold a07927
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00025.pow 2)).mul (mod_a07868.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a07871.pow 1)))
  apply h.trans
  refine ⟨q07927, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07927, r07927, r00000, r00003, r00004, r00009, r00025, r07868, r07871, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07928 : UPoly := (Polynomial.C ((3122004866224464738976 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((398236646568905537528 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((11621528631826956398944 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((455421389647953993608 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((45975197623079495552 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-275841105503656604368 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q07928 : UPoly := (Polynomial.C ((21800315321633338880 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((234640026846384363968 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((74630022338281702400 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((2182812714382233344 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-60861168051523324736 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((106050197809515776 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((32584624155605312 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-102784415265605632 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-30589954648601984 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-235040788480 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((-4885672922283776 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((-147208886149120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((-12917821952 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 12)
lemma mod_a07928 : Modulo (spec a07928) r07928 := by
  have h : Modulo (spec a07928) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r00000 ^ 5 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00032 ^ 1 * r07868 ^ 1 * r07870 ^ 1 * r07927 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07926 ^ 1)) := by
    unfold a07928
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00032.pow 1)).mul (mod_a07868.pow 1)).mul (mod_a07870.pow 1)).mul (mod_a07927.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07926.pow 1)))
  apply h.trans
  refine ⟨q07928, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07928, r07928, r00000, r00001, r00003, r00004, r00032, r07868, r07870, r07926, r07927, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07929 : UPoly := (Polynomial.C ((18267123483136 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((13751218179173504 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((401515305074336 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((5871953345528 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-148841087517376 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-44017166106208 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07929 : UPoly := (Polynomial.C ((-415161897344 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-104172750130880 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-250288345912 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07929 : Modulo (spec a07929) r07929 := by
  have h : Modulo (spec a07929) ((Polynomial.C ((-1 : ℂ) / (54 : ℂ)) * r00000 ^ 3 * r00002 ^ 1 * r00003 ^ 2 * r07920 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 5 * r00004 ^ 1 * r00005 ^ 1 * r00009 ^ 1 * r00014 ^ 4 * r00025 ^ 1 * r07873 ^ 1 * r07895 ^ 1)) := by
    unfold a07929
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (54 : ℂ)))).mul (mod_a00000.pow 3)).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 2)).mul (mod_a07920.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 5)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 4)).mul (mod_a00025.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07895.pow 1)))
  apply h.trans
  refine ⟨q07929, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07929, r07929, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00025, r07873, r07895, r07920, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07930 : UPoly := (Polynomial.C ((15996742443946768 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1683781036450892 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((38612777203083040 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((13726624824955976 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((359883423081860 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-13865667417500432 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07930 : UPoly := (Polynomial.C ((-25695069366116 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((4043808560224 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-152675462252656 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-4600277692160 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-403681936 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a07930 : Modulo (spec a07930) r07930 := by
  have h : Modulo (spec a07930) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 1 * r00003 ^ 1 * r07870 ^ 1 * r07927 ^ 1) + (Polynomial.C ((1 : ℂ) / (2 : ℂ)) * r00000 ^ 1 * r00004 ^ 1 * r07929 ^ 1)) := by
    unfold a07930
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 1)).mul (mod_a00003.pow 1)).mul (mod_a07870.pow 1)).mul (mod_a07927.pow 1)).add ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a07929.pow 1)))
  apply h.trans
  refine ⟨q07930, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07930, r07930, r00000, r00002, r00003, r00004, r07870, r07927, r07929, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07931 : UPoly := (Polynomial.C ((43708068127142506345664 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((5575313051964677525392 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((162701400845577389585216 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((6375899455071355910512 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((643652766723112937728 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-3861775477051192461152 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 5)
def q07931 : UPoly := (Polynomial.C ((-25690012733431340816 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1362062962525030144 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((41179860223404045248 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((247186831190144 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-5758134769309760 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((221850678680006912 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
lemma mod_a07931 : Modulo (spec a07931) r07931 := by
  have h : Modulo (spec a07931) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00001 ^ 4 * r00002 ^ 3 * r00004 ^ 1 * r00005 ^ 2 * r00014 ^ 2 * r07868 ^ 1 * r07930 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07889 ^ 1 * r07928 ^ 1)) := by
    unfold a07931
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a07868.pow 1)).mul (mod_a07930.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07889.pow 1)).mul (mod_a07928.pow 1)))
  apply h.trans
  refine ⟨q07931, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07931, r07931, r00001, r00002, r00004, r00005, r00014, r07868, r07889, r07928, r07930, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07932 : UPoly := (Polynomial.C ((-1682311923772255673517995104 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-158233198132058891884346920 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-6251224881598750240637800 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-116142787641944339050245776 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-26818030320108113195103200 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-10161379018660791711584 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 5)
def q07932 : UPoly := (Polynomial.C ((-1215624959009047250416 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-24819518611710732928 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-20997084729756928 : ℂ) / (2187 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-10511205046678188032 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-53274790283394944 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-265745500964864 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-32423968768232704 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-325625115676672 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-771490098944 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 8)
lemma mod_a07932 : Modulo (spec a07932) r07932 := by
  have h : Modulo (spec a07932) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00012 ^ 1 * r07914 ^ 1 * r07917 ^ 1) + (Polynomial.C ((1 : ℂ) / (54 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00014 ^ 3 * r07870 ^ 1 * r07873 ^ 1 * r07916 ^ 1)) := by
    unfold a07932
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00012.pow 1)).mul (mod_a07914.pow 1)).mul (mod_a07917.pow 1)).add (((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (54 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00014.pow 3)).mul (mod_a07870.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07916.pow 1)))
  apply h.trans
  refine ⟨q07932, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07932, r07932, r00001, r00002, r00004, r00005, r00012, r00014, r07870, r07873, r07914, r07916, r07917, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07933 : UPoly := (Polynomial.C ((-2300447757824 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1550022381959968 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((48957459713064 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((453544258752 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((103863548921696 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((2194154873468 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07933 : UPoly := (Polynomial.C ((6863110144 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((806827679744 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((8251768832 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((20754432 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3)
lemma mod_a07933 : Modulo (spec a07933) r07933 := by
  have h : Modulo (spec a07933) ((Polynomial.C ((-27 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00009 ^ 1 * r00025 ^ 1 * r07873 ^ 1 * r07922 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07920 ^ 1)) := by
    unfold a07933
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-27 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00009.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07922.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07920.pow 1)))
  apply h.trans
  refine ⟨q07933, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07933, r07933, r00000, r00009, r00025, r07873, r07920, r07922, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07934 : UPoly := (Polynomial.C ((336863841088 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((32210491520 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((339222340 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((202171809952 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((460460140 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((26245312 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07934 : UPoly := (Polynomial.C ((1575833840 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((15826048 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((37496 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2)
lemma mod_a07934 : Modulo (spec a07934) r07934 := by
  have h : Modulo (spec a07934) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00009 ^ 1 * r07870 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07924 ^ 1)) := by
    unfold a07934
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00009.pow 1)).mul (mod_a07870.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07924.pow 1)))
  apply h.trans
  refine ⟨q07934, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07934, r07934, r00009, r07870, r07924, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07935 : UPoly := (Polynomial.C ((-526684591616 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2232760173792 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-517855261656 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-40626056000 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((351582226272 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((72354548348 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07935 : UPoly := (Polynomial.C ((-13437599744 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0)
lemma mod_a07935 : Modulo (spec a07935) r07935 := by
  have h : Modulo (spec a07935) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07933 ^ 1) + (Polynomial.C ((27 : ℂ) / (1 : ℂ)) * r00000 ^ 1 * r00025 ^ 1 * r07873 ^ 1 * r07934 ^ 1)) := by
    unfold a07935
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07933.pow 1)).add (((((Modulo.refl (Polynomial.C ((27 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 1)).mul (mod_a00025.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07934.pow 1)))
  apply h.trans
  refine ⟨q07935, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07935, r07935, r00000, r00025, r07873, r07933, r07934, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07936 : UPoly := (Polynomial.C ((-434343533312 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-13587502624 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-277374330328 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-33868578624 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-751377536 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((44042491004 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07936 : UPoly := (Polynomial.C ((-699553472 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-16806614528 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1694502400 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-27756576 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((2924049920 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((216832 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-118784 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((18603648 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a07936 : Modulo (spec a07936) r07936 := by
  have h : Modulo (spec a07936) ((Polynomial.C ((-1 : ℂ) / (2 : ℂ)) * r00000 ^ 5 * r00001 ^ 3 * r00003 ^ 2 * r00004 ^ 2 * r00032 ^ 1 * r07873 ^ 1 * r07927 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07935 ^ 1)) := by
    unfold a07936
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (2 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 3)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00032.pow 1)).mul (mod_a07873.pow 1)).mul (mod_a07927.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07935.pow 1)))
  apply h.trans
  refine ⟨q07936, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07936, r07936, r00000, r00001, r00003, r00004, r00032, r07873, r07927, r07935, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07937 : UPoly := (Polynomial.C ((-31384928256 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-473497600 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-67824222208 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1966870528 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-14221312 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((8686108672 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07937 : UPoly := (Polynomial.C ((237764608 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1785856 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((513806336 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((7405568 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((24576 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((7471104 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((49152 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((32768 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 8)
lemma mod_a07937 : Modulo (spec a07937) r07937 := by
  have h : Modulo (spec a07937) ((Polynomial.C ((-1 : ℂ) / (4 : ℂ)) * r00000 ^ 5 * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 2 * r00004 ^ 2 * r00005 ^ 2 * r00009 ^ 1 * r00014 ^ 2 * r00025 ^ 1 * r07868 ^ 1 * r07873 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07895 ^ 1 * r07920 ^ 1)) := by
    unfold a07937
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (4 : ℂ)))).mul (mod_a00000.pow 5)).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 2)).mul (mod_a00004.pow 2)).mul (mod_a00005.pow 2)).mul (mod_a00009.pow 1)).mul (mod_a00014.pow 2)).mul (mod_a00025.pow 1)).mul (mod_a07868.pow 1)).mul (mod_a07873.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07895.pow 1)).mul (mod_a07920.pow 1)))
  apply h.trans
  refine ⟨q07937, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07937, r07937, r00000, r00001, r00002, r00003, r00004, r00005, r00009, r00014, r00025, r07868, r07873, r07895, r07920, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07938 : UPoly := (Polynomial.C ((-868687066624 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-27175005248 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-554748660656 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-67737157248 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1502755072 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((88084982008 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07938 : UPoly := (Polynomial.C ((-112552576 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-15843408 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1778257280 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((4759328 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-59392 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((9301824 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
lemma mod_a07938 : Modulo (spec a07938) r07938 := by
  have h : Modulo (spec a07938) ((Polynomial.C ((-1 : ℂ) / (2 : ℂ)) * r00001 ^ 4 * r00002 ^ 4 * r00003 ^ 1 * r00004 ^ 1 * r00005 ^ 2 * r00014 ^ 2 * r07873 ^ 1 * r07927 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07937 ^ 1)) := by
    unfold a07938
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (2 : ℂ)))).mul (mod_a00001.pow 4)).mul (mod_a00002.pow 4)).mul (mod_a00003.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 2)).mul (mod_a00014.pow 2)).mul (mod_a07873.pow 1)).mul (mod_a07927.pow 1)).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07937.pow 1)))
  apply h.trans
  refine ⟨q07938, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07938, r07938, r00001, r00002, r00003, r00004, r00005, r00014, r07873, r07927, r07937, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07939 : UPoly := (Polynomial.C ((-6080809466368 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-190225036736 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-3883240624592 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-474160100736 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-10519285504 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((616594874056 : ℂ) / (1 : ℂ)) * Polynomial.X ^ 5)
def q07939 : UPoly := 0
lemma mod_a07939 : Modulo (spec a07939) r07939 := by
  have h : Modulo (spec a07939) ((Polynomial.C ((-1 : ℂ) / (1 : ℂ)) * r07938 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07889 ^ 1 * r07936 ^ 1)) := by
    unfold a07939
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-1 : ℂ) / (1 : ℂ)))).mul (mod_a07938.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07889.pow 1)).mul (mod_a07936.pow 1)))
  apply h.trans
  refine ⟨q07939, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07939, r07939, r07889, r07936, r07938, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07940 : UPoly := (Polynomial.C ((165016763881961227750769262847946592191864216576 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((206684402937951000203906913736370626506010535936 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-90746755081646905891281568010481735242522590114496 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-11572383109249190258222669932662027073812739547584 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-616090601363818053333557673953752729085903879360 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-439733050807654094500056299105397216049949050304 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 5)
def q07940 : UPoly := (Polynomial.C ((-6041633738508396592872347568416941988813143552 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-30783434767262323909244053633375291156152908032 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((376046873704663742054489508522570649319636981248 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((6880240554936670131484047937823944790757362048 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-66756559071919040345333391310677490459047808 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((104375396384427221197473754995195926253452800 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((8865785537433114099057273544619856717407488 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((43037565956867465998201876989453222017536 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((1031310535095697705426407040639448782386688 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((29262502228628498543384435043025728601088 : ℂ) / (6561 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((852379005487883741100678322543633816576 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((10309743724673068954659827697781267161088 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((264527583769403790689941423665287426048 : ℂ) / (19683 : ℂ)) * Polynomial.X ^ 12) + (Polynomial.C ((100247267459942907827030162500235264 : ℂ) / (729 : ℂ)) * Polynomial.X ^ 13)
lemma mod_a07940 : Modulo (spec a07940) r07940 := by
  have h : Modulo (spec a07940) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00014 ^ 3 * r07868 ^ 1 * r07932 ^ 1 * r07939 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07918 ^ 1 * r07931 ^ 1)) := by
    unfold a07940
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00014.pow 3)).mul (mod_a07868.pow 1)).mul (mod_a07932.pow 1)).mul (mod_a07939.pow 1)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07918.pow 1)).mul (mod_a07931.pow 1)))
  apply h.trans
  refine ⟨q07940, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07940, r07940, r00014, r07868, r07918, r07931, r07932, r07939, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07941 : UPoly := (Polynomial.C ((195530823796702601996813741082098145286696831059968 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((26517655587797679405717645808867828931735056282624 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1353748322180684516295600459459583684091325126203264 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-518043439439548038798607982328900585064960533167744 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3065320479342582003652355768416674439908881559808 : ℂ) / (59049 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6482232579859865628371578582562193252152438487296 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 5)
def q07941 : UPoly := (Polynomial.C ((-19484087232804403947707641882783238098611692416000 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-388109645182915769548023234896925755294012802304 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((12087309104425216294277393688631063137093118224896 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((310516603597082445937307050381852130755896863872 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1059544622267139009458155526971629401312872832 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-4366904950153020264151240688001344480980480 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-125500221646056327099396473773061708343296 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-652009634446299736807388809832236186112 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 7) + (Polynomial.C ((-43164070712116878164209428162470739647488 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 8) + (Polynomial.C ((-1246361574525005290232776618150567236608 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 9) + (Polynomial.C ((-4173779115652173795990043017049391104 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 10) + (Polynomial.C ((-47954148726086258171621330232213463040 : ℂ) / (177147 : ℂ)) * Polynomial.X ^ 11) + (Polynomial.C ((-3769126066443395039040322736616298496 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 12) + (Polynomial.C ((-39837993500140828433483721495842816 : ℂ) / (531441 : ℂ)) * Polynomial.X ^ 13)
lemma mod_a07941 : Modulo (spec a07941) r07941 := by
  have h : Modulo (spec a07941) ((Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07931 ^ 1 * r07932 ^ 1) + (Polynomial.C ((1 : ℂ) / (54 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r00014 ^ 3 * r07918 ^ 1 * r07939 ^ 1)) := by
    unfold a07941
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07931.pow 1)).mul (mod_a07932.pow 1)).add ((((((((Modulo.refl (Polynomial.C ((1 : ℂ) / (54 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a00014.pow 3)).mul (mod_a07918.pow 1)).mul (mod_a07939.pow 1)))
  apply h.trans
  refine ⟨q07941, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07941, r07941, r00001, r00002, r00004, r00005, r00014, r07918, r07931, r07932, r07939, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07942 : UPoly := (Polynomial.C ((1156364075476910686624598283172794901156573905647610113565041602186730718832362284646898856383042675474432 : ℂ) / (2541865828329 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1349050333068426968177477095060545971798013463993731249999162175853320531780267220752554191867565538623488 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((416341224586930238049906863641685379667671902420785717289083451291377961048855247663730809318406431932416 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((3928630784617537425597943829526467555403339374472681644205896109943004637293049215443148895540692762624 : ℂ) / (282429536481 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-96071429579076447966495707765585617785226243772980465974572424344544011715915339770777182415577114558464 : ℂ) / (847288609443 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-223639957597321020909099219068757122799836192016398143688391888447453893983816164667324161662893787561984 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 5)
def q07942 : UPoly := (Polynomial.C ((-26421771517828540228735170504365443773469489104257416681912356647883210456625058094104995325782208233472 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-10032640712296277934516462519843623836600488138891097325295988554335943193583313430509149652831318605824 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1129158453572559927577037757477308848882071350317805748479122208258283951895282012905943729776795238400 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-57943438056488012726266316894208290746404360560377358396519411339183164081419800143969478828031377408 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-20422172321250681389152860399429604661697420983336551992579895368823390188871224242018060164238295040 : ℂ) / (7625597484987 : ℂ)) * Polynomial.X ^ 4)
lemma mod_a07942 : Modulo (spec a07942) r07942 := by
  have h : Modulo (spec a07942) ((Polynomial.C ((-1 : ℂ) / (54 : ℂ)) * r00001 ^ 9 * r00002 ^ 3 * r00004 ^ 3 * r00005 ^ 3 * r07940 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r07868 ^ 1 * r07941 ^ 2)) := by
    unfold a07942
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (54 : ℂ)))).mul (mod_a00001.pow 9)).mul (mod_a00002.pow 3)).mul (mod_a00004.pow 3)).mul (mod_a00005.pow 3)).mul (mod_a07940.pow 2)).add (((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a07868.pow 1)).mul (mod_a07941.pow 2)))
  apply h.trans
  refine ⟨q07942, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07942, r07942, r00001, r00002, r00004, r00005, r07868, r07940, r07941, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07947 : UPoly := (Polynomial.C ((-7 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 0)
def q07947 : UPoly := 0
lemma mod_a07947 : Modulo (spec a07947) r07947 := by
  have h : Modulo (spec a07947) ((Polynomial.C ((-3 : ℂ) / (1 : ℂ)) * r00005 ^ 6) + (Polynomial.C ((-1 : ℂ) / (6 : ℂ)) * r00001 ^ 3 * r00002 ^ 1 * r00004 ^ 1 * r00005 ^ 1) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00002 ^ 6)) := by
    unfold a07947
    simp only [map_add, map_mul, map_pow, spec_C]
    exact ((((Modulo.refl (Polynomial.C ((-3 : ℂ) / (1 : ℂ)))).mul (mod_a00005.pow 6)).add (((((Modulo.refl (Polynomial.C ((-1 : ℂ) / (6 : ℂ)))).mul (mod_a00001.pow 3)).mul (mod_a00002.pow 1)).mul (mod_a00004.pow 1)).mul (mod_a00005.pow 1))).add ((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00002.pow 6)))
  apply h.trans
  refine ⟨q07947, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07947, r07947, r00001, r00002, r00004, r00005, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def r07960 : UPoly := (Polynomial.C ((-64159617192088885504 : ℂ) / (9 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-7923309613857244544 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-138051263827264688 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-15254929164660447232 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-60733891087957120 : ℂ) / (3 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-8130823351107664 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 5)
def q07960 : UPoly := (Polynomial.C ((-291783861247621120 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8663530740780544 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-105058658414848 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2194614056345728 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-10648285549024 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-79286038016 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 5) + (Polynomial.C ((-6765326159296 : ℂ) / (81 : ℂ)) * Polynomial.X ^ 6) + (Polynomial.C ((-21013464064 : ℂ) / (27 : ℂ)) * Polynomial.X ^ 7)
lemma mod_a07960 : Modulo (spec a07960) r07960 := by
  have h : Modulo (spec a07960) ((Polynomial.C ((-36 : ℂ) / (1 : ℂ)) * r07824 ^ 2) + (Polynomial.C ((1 : ℂ) / (1 : ℂ)) * r00000 ^ 2 * r00003 ^ 1 * r00015 ^ 2 * r00034 ^ 1)) := by
    unfold a07960
    simp only [map_add, map_mul, map_pow, spec_C]
    exact (((Modulo.refl (Polynomial.C ((-36 : ℂ) / (1 : ℂ)))).mul (mod_a07824.pow 2)).add (((((Modulo.refl (Polynomial.C ((1 : ℂ) / (1 : ℂ)))).mul (mod_a00000.pow 2)).mul (mod_a00003.pow 1)).mul (mod_a00015.pow 2)).mul (mod_a00034.pow 1)))
  apply h.trans
  refine ⟨q07960, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [f, q07960, r07960, r00000, r00003, r00015, r00034, r07824, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring

def u00012 : UPoly := 0
def v00012 : UPoly := (Polynomial.C ((-1 : ℂ) / (63 : ℂ)) * Polynomial.X ^ 0)
lemma bezout_00012 : u00012*f+v00012*r00012=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00012, f, v00012, r00012, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00012 : IsCoprime f (spec a00012) :=
  coprime_of_modulo mod_a00012 bezout_00012

def u00013 : UPoly := 0
def v00013 : UPoly := (Polynomial.C ((-3 : ℂ) / (188 : ℂ)) * Polynomial.X ^ 0)
lemma bezout_00013 : u00013*f+v00013*r00013=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00013, f, v00013, r00013, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00013 : IsCoprime f (spec a00013) :=
  coprime_of_modulo mod_a00013 bezout_00013

def u00014 : UPoly := (Polynomial.C ((5825050753 : ℂ) / (55568012926912 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-7479409 : ℂ) / (6946001615864 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((231009 : ℂ) / (27784006463456 : ℂ)) * Polynomial.X ^ 2)
def v00014 : UPoly := (Polynomial.C ((279587276671 : ℂ) / (55568012926912 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-176986015 : ℂ) / (6946001615864 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((3609023 : ℂ) / (27784006463456 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-182025617 : ℂ) / (3473000807932 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((7479409 : ℂ) / (13892003231728 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-231009 : ℂ) / (55568012926912 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00014 : u00014*f+v00014*r00014=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00014, f, v00014, r00014, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00014 : IsCoprime f (spec a00014) :=
  coprime_of_modulo mod_a00014 bezout_00014

def u00015 : UPoly := (Polynomial.C ((628067265907 : ℂ) / (13469086913913536 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-402635649 : ℂ) / (841817932119596 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((37208371 : ℂ) / (10101815185435152 : ℂ)) * Polynomial.X ^ 2)
def v00015 : UPoly := (Polynomial.C ((68296847116397 : ℂ) / (13469086913913536 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-43414890237 : ℂ) / (1683635864239192 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((885746477 : ℂ) / (6734543456956768 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-29438908947 : ℂ) / (841817932119596 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1207906947 : ℂ) / (3367271728478384 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-37208371 : ℂ) / (13469086913913536 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00015 : u00015*f+v00015*r00015=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00015, f, v00015, r00015, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00015 : IsCoprime f (spec a00015) :=
  coprime_of_modulo mod_a00015 bezout_00015

def u00018 : UPoly := (Polynomial.C ((5478607514877262269389849377498564270006367098519706977 : ℂ) / (6040588663076375158957478079243628096459537955159504584704 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-4819074739276798775750833310494879772503780986801089 : ℂ) / (755073582884546894869684759905453512057442244394938073088 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((490850691875220573523906488493232482598951904587 : ℂ) / (11104023277713924924554187645668434000844738888160854016 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((661086635487578893337787781448880517631041500431 : ℂ) / (377536791442273447434842379952726756028721122197469036544 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((6847762516128568537457198226254960346162555485 : ℂ) / (755073582884546894869684759905453512057442244394938073088 : ℂ)) * Polynomial.X ^ 4)
def v00018 : UPoly := (Polynomial.C ((802039306493495926473427618239111404195808623993 : ℂ) / (447451012079731493256109487351379858997002811493296635904 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1538989295294473356296968641571398115881643833 : ℂ) / (55931376509966436657013685918922482374625351436662079488 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((63021242069397080982433454540887241817492281 : ℂ) / (223725506039865746628054743675689929498501405746648317952 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-1661511099747309863825627822464768244988076455 : ℂ) / (27965688254983218328506842959461241187312675718331039744 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((125904165835754057497341626199896513731839399 : ℂ) / (111862753019932873314027371837844964749250702873324158976 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-6141491045855218419244123969735390444988839 : ℂ) / (447451012079731493256109487351379858997002811493296635904 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00018 : u00018*f+v00018*r00018=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00018, f, v00018, r00018, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00018 : IsCoprime f (spec a00018) :=
  coprime_of_modulo mod_a00018 bezout_00018

def u00026 : UPoly := (Polynomial.C ((220989199835494844641523982210973830064446907024035517064401213004259243608751143716028831965691048949221820369032918389108079447 : ℂ) / (39089338739143915906556024134254279604106150321108615758981122561067142415596627302359253970575770972839255813431509698846323113984 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-142613366392295737840607156443162872317914448951977695317693441600573698889747892232625048750739686390831125066827838215676189 : ℂ) / (2443083671196494744159751508390892475256634395069288484936320160066696400974789206397453373160985685802453488339469356177895194624 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1440362564777472227262809030076068060683100885974964149092577676975986281220668995608543058574405630665557604182124456252123 : ℂ) / (2299372867008465641562119066720839976712126489476977397587124856533361318564507488374073762975045351343485636084206452873313124352 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((11577621321517144898043694682823297242950971646540208515776483246883422823572846558164517373766009070435619883656954508644015 : ℂ) / (78178677478287831813112048268508559208212300642217231517962245122134284831193254604718507941151541945678511626863019397692646227968 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((435914380109799109422775011515076623547949338890084421028832581358317711629317649531307014085814656582907557567056484829 : ℂ) / (80430738146386658243942436490235143218325412183351061232471445598903585217277010910204226276904878544936740356854958228078854144 : ℂ)) * Polynomial.X ^ 4)
def v00026 : UPoly := (Polynomial.C ((-5188969407605407593731449094379618572978571565237624672482834973122141358053249514000148920778219656352069587 : ℂ) / (214481968390364421983846497307293715248867765822269496619923854930409560579405362427211270071746342786497974284946555274876944384 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((8600597205223964539217653277188956722795376791633084652223716294600508803755828875452778379854170599635889 : ℂ) / (8936748682931850915993604054470571468702823575927895692496827288767065024141890101133802919656097616104082261872773136453206016 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2296501858211947369492149508223464877516979881216967308928212983206425760263739383631889499217497344730899 : ℂ) / (107240984195182210991923248653646857624433882911134748309961927465204780289702681213605635035873171393248987142473277637438472192 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((6242658221449847580371480280111163622183637626948125657176918703708413787140666997852357866190772289476453 : ℂ) / (1489458113821975152665600675745095244783803929321315948749471214794510837356981683522300486609349602684013710312128856075534336 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-3770536197429316647415022251316892020202313559754329210993252752239928281565022779017813890415443642223151 : ℂ) / (17873497365863701831987208108941142937405647151855791384993654577534130048283780202267605839312195232208164523745546272906412032 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1324657501604754703165972529372891248020506281512355118427066726353293093408136018721461461225667746622093 : ℂ) / (214481968390364421983846497307293715248867765822269496619923854930409560579405362427211270071746342786497974284946555274876944384 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00026 : u00026*f+v00026*r00026=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00026, f, v00026, r00026, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00026 : IsCoprime f (spec a00026) :=
  coprime_of_modulo mod_a00026 bezout_00026

def u00033 : UPoly := (Polynomial.C ((189855742906123361643125492304089182633824554295013423083237257563482987037956535401313068587760139331845752755730137155275965843 : ℂ) / (24540453511983157636319243554727579076844768064654950965153952785551890468209559426552241327341117095648567562258421225945353420800 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((2812596930371931489741303710501392338233161457959136964741719636177916484142192995440457572463214035759585782060114312831364781 : ℂ) / (6135113377995789409079810888681894769211192016163737741288488196387972617052389856638060331835279273912141890564605306486338355200 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-13155219109631387985089066942289749201227503945229859707589256291780120250066292137568126534869175033327575235991306857151853643 : ℂ) / (147242721071898945817915461328365474461068608387929705790923716713311342809257356559313447964046702573891405373550527355672120524800 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((1704853484272988231619090700327607251730685244087379312173731370776421622565449942679885384239170326474011342341755035473118747 : ℂ) / (6135113377995789409079810888681894769211192016163737741288488196387972617052389856638060331835279273912141890564605306486338355200 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((96886144212931714164985744823409235317580238965997598195306413995721782620388043863928502790203482108410048054614669195696445 : ℂ) / (2944854421437978916358309226567309489221372167758594115818474334266226856185147131186268959280934051477828107471010547113442410496 : ℂ)) * Polynomial.X ^ 4)
def v00033 : UPoly := (Polynomial.C ((17260512086862771960852849390224585888251752043287107157835944672277291112034933064840871168242373863552243137 : ℂ) / (32720604682644210181758991406303438769126357419539934620205270380735853957612745902069655103121489460864756749677894967927137894400 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-553895425374149563034542316755166587839569244289939465013066224209331004475197831020809850902003461024249217 : ℂ) / (4090075585330526272719873925787929846140794677442491827525658797591981744701593237758706887890186182608094593709736870990892236800 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((5437382751462192342390221109449413073305399753163704303270337469518155176013342240700669052669870934115053953 : ℂ) / (16360302341322105090879495703151719384563178709769967310102635190367926978806372951034827551560744730432378374838947483963568947200 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((15606102291410034887755427747726266085325415985089737060592083844038016384995174215640294373527970611047841 : ℂ) / (2045037792665263136359936962893964923070397338721245913762829398795990872350796618879353443945093091304047296854868435495446118400 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-101407308742405468499421312626312415691317975801374257323610428512846631948704949919083277194027171106302369 : ℂ) / (8180151170661052545439747851575859692281589354884983655051317595183963489403186475517413775780372365216189187419473741981784473600 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((543901795715143955711665708704280967111820327570424808151717264068202643277291705859489444160595255446447521 : ℂ) / (32720604682644210181758991406303438769126357419539934620205270380735853957612745902069655103121489460864756749677894967927137894400 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00033 : u00033*f+v00033*r00033=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00033, f, v00033, r00033, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00033 : IsCoprime f (spec a00033) :=
  coprime_of_modulo mod_a00033 bezout_00033

def u00034 : UPoly := (Polynomial.C ((231150047141811113500417538942641203369178709424251379684115547957702079953 : ℂ) / (30513999476871570189971937053955893466226305719174485827617794390604233310208 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((1413404585317722844599470034392924606454448261056321948374092956033057077 : ℂ) / (15256999738435785094985968526977946733113152859587242913808897195302116655104 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((25310875913355628070856907196733518726034966476062706865902112168654413 : ℂ) / (61027998953743140379943874107911786932452611438348971655235588781208466620416 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((50679135128712557250309211046713472806394707119672261989561030027867055727 : ℂ) / (244111995814972561519775496431647147729810445753395886620942355124833866481664 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((9837785067677102639454808581399093876750405371966724137817610945499593 : ℂ) / (5085666579478595031661989508992648911037717619862414304602965731767372218368 : ℂ)) * Polynomial.X ^ 4)
def v00034 : UPoly := (Polynomial.C ((1424598365546146984365818780356794994501736350594877839329789673 : ℂ) / (54247110181105013671061221429254921717735654611865752582431634472185303662592 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-60381463496834655945318176440799226691832283707005726776489 : ℂ) / (6780888772638126708882652678656865214716956826483219072803954309023162957824 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1530588398819103986910324096277458786827295219606394767561013417 : ℂ) / (27123555090552506835530610714627460858867827305932876291215817236092651831296 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2839484823524600757918828854918524499006887963953156070819383 : ℂ) / (3390444386319063354441326339328432607358478413241609536401977154511581478912 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((615870768811130601427969234816999815148969570481275222714935 : ℂ) / (13561777545276253417765305357313730429433913652966438145607908618046325915648 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((479401772055270834511834439985490634515138222423731721814471113 : ℂ) / (54247110181105013671061221429254921717735654611865752582431634472185303662592 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00034 : u00034*f+v00034*r00034=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00034, f, v00034, r00034, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00034 : IsCoprime f (spec a00034) :=
  coprime_of_modulo mod_a00034 bezout_00034

def u00042 : UPoly := (Polynomial.C ((56831701461200502650972647407485051950885646639100251107 : ℂ) / (62667824265032575564274881036804137231293678369624069160960 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2313274044346185488121740188000311128092671140777826613 : ℂ) / (250671297060130302257099524147216548925174713478496276643840 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((71224811733371047378624624631432131455607224731713013 : ℂ) / (1002685188240521209028398096588866195700698853913985106575360 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((246501718708712216375478094148507621989130453692219 : ℂ) / (125335648530065151128549762073608274462587356739248138321920 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((3193116187666755075054241312361261353837191130247 : ℂ) / (501342594120260604514199048294433097850349426956992553287680 : ℂ)) * Polynomial.X ^ 4)
def v00042 : UPoly := (Polynomial.C ((69638610676095153169748296782665313863561193608593 : ℂ) / (37136488453352637371422151725513562803729587181999448391680 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-26224023523908293827497080535378027964611828189 : ℂ) / (928412211333815934285553793137839070093239679549986209792 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((5302610391891454516726870670681305314476473681 : ℂ) / (18568244226676318685711075862756781401864793590999724195840 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-144254303480739391652142792125252959270606326927 : ℂ) / (2321030528334539835713884482844597675233099198874965524480 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((11826950377699364337714358213439440587533455503 : ℂ) / (9284122113338159342855537931378390700932396795499862097920 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-607402736858808269936131122762271514901501071 : ℂ) / (37136488453352637371422151725513562803729587181999448391680 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00042 : u00042*f+v00042*r00042=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00042, f, v00042, r00042, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00042 : IsCoprime f (spec a00042) :=
  coprime_of_modulo mod_a00042 bezout_00042

def u00100 : UPoly := (Polynomial.C ((61727885253837737340495835368561407471260164502658880486794430633675977 : ℂ) / (19938441723710437759268759312946887565420044397743560414342383493479137280 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-25614807887745009164201879356765897652255008560193094607209669219315437 : ℂ) / (478522601369050506222450223510725301570081065545845449944217203843499294720 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((46769740705751166760657315331818442017237849244073509346447222262159 : ℂ) / (59815325171131313277806277938840662696260133193230681243027150480437411840 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((10075632923204300700701703351689150604076282526097134192185015830397 : ℂ) / (239261300684525253111225111755362650785040532772922724972108601921749647360 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((2243589015236289378564696797964352803831979707739146469558683163 : ℂ) / (5981532517113131327780627793884066269626013319323068124302715048043741184 : ℂ)) * Polynomial.X ^ 4)
def v00100 : UPoly := (Polynomial.C ((-280782721297316371129546290687654809422357343804209352849377977 : ℂ) / (5671378979188746740414224871238225796386145962024834962301833527034065715200 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((881274635436820466850125293201120676490167331707878668741753 : ℂ) / (708922372398593342551778108904778224548268245253104370287729190879258214400 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-53421792770923808178571303940093471453696961933940617070713 : ℂ) / (2835689489594373370207112435619112898193072981012417481150916763517032857600 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((273002391023207508640208947855146216561994409771378966082171 : ℂ) / (70892237239859334255177810890477822454826824525310437028772919087925821440 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-207358906541815382516417928861711716817046959741431448264807 : ℂ) / (1417844744797186685103556217809556449096536490506208740575458381758516428800 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((3948564831336221657430399307462557974514970936605148863099 : ℂ) / (1134275795837749348082844974247645159277229192404966992460366705406813143040 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00100 : u00100*f+v00100*r00100=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00100, f, v00100, r00100, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00100 : IsCoprime f (spec a00100) :=
  coprime_of_modulo mod_a00100 bezout_00100

def u00101 : UPoly := (Polynomial.C ((5767369711253520887430165312476724114898307221950780685655841216125757724262654311377359800481189458773780884945169318274790365258969619948190154746191154705547 : ℂ) / (761313093571799961470988444157952215676486846853003993733304345092363257878768691153214577651051220007554422039111096178790755315601124813337023428495190343548928 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((3501001599176053505609022980451552098392740155975793070492075935550945798238329564869635567217876481285810326526331182565917197784731288588951277336362830699 : ℂ) / (47582068348237497591936777759872013479780427928312749608331521568272703617423043197075911103190701250472151377444443511174422207225070300833563964280949396471808 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1751178849053975685211078960709710107423166911637418787603625658173764592684347973457786490223483717791922124379181197050444927049565247871803785884090383723 : ℂ) / (1141969640357699942206482666236928323514730270279505990599956517638544886818153036729821866476576830011331633058666644268186132973401687220005535142742785515323392 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((114400745431240740505144391809782354520461682957895358511695283616803419366272740491896315915362224617098545992288247703518857120413619735619078453369064278205 : ℂ) / (380656546785899980735494222078976107838243423426501996866652172546181628939384345576607288825525610003777211019555548089395377657800562406668511714247595171774464 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4570880151361301750930174063232097734409401315681265287525757837027812463611606693810306371383044260853624632485007054333797799975202061506225691752604021745 : ℂ) / (570984820178849971103241333118464161757365135139752995299978258819272443409076518364910933238288415005665816529333322134093066486700843610002767571371392757661696 : ℂ)) * Polynomial.X ^ 4)
def v00101 : UPoly := (Polynomial.C ((925711963210785031691862398697039783924714583206750111551265472060912455844311287059596006143907996004185207515756880697723435941065223 : ℂ) / (56393562486799997145999144011700164124184210878000295832096618154989870953982866011349227974151942222781809039934155272503018912266749986173112846555199284707328 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1974258066249314766863643287880877477320478125472336665942193279665853626653648919075995248022232416647888493368347535230769722744903 : ℂ) / (7049195310849999643249893001462520515523026359750036979012077269373733869247858251418653496768992777847726129991769409062877364033343748271639105819399910588416 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((1467783074818473860667114843594547237022606214518709499959269327742861695193583165547358964775681659439065081980630021981818024888648775 : ℂ) / (28196781243399998572999572005850082062092105439000147916048309077494935476991433005674613987075971111390904519967077636251509456133374993086556423277599642353664 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-6757920140041857222576584283778212253645946669900204591663379550089595724014684303113176064687645705924207844502363376585714466545369 : ℂ) / (3524597655424999821624946500731260257761513179875018489506038634686866934623929125709326748384496388923863064995884704531438682016671874135819552909699955294208 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((617025315411099897009779598491215726968064188906795277327924793871015756549828456779313542496295558774938919580096529619896699058905 : ℂ) / (14098390621699999286499786002925041031046052719500073958024154538747467738495716502837306993537985555695452259983538818125754728066687496543278211638799821176832 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((192428271758765787589850924099880824232079031167798397140169736982221632674329693258089622227527071465043040560801481050131335293430055 : ℂ) / (56393562486799997145999144011700164124184210878000295832096618154989870953982866011349227974151942222781809039934155272503018912266749986173112846555199284707328 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00101 : u00101*f+v00101*r00101=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00101, f, v00101, r00101, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00101 : IsCoprime f (spec a00101) :=
  coprime_of_modulo mod_a00101 bezout_00101

def u00103 : UPoly := (Polynomial.C ((5723997324876196085720486138420860803941714236500790660270645548408823560073942956607649 : ℂ) / (6295332854337360287738506971337927184295802728920843135951582659038102173510864184035770368 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-3437551895806769621635670937531366468206154834389066735595482723531795368198690168223 : ℂ) / (393458303396085017983656685708620449018487670557552695996973916189881385844429011502235648 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((207928599768852104889171901876870571084701558675967621405232373568457846407944786877 : ℂ) / (3147666427168680143869253485668963592147901364460421567975791329519051086755432092017885184 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((381056415372461910524125499210681492644705429524947205674218582848386051852344385 : ℂ) / (196729151698042508991828342854310224509243835278776347998486958094940692922214505751117824 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((475252306506542337461251121015772884053424755133201213302540668084908202116215 : ℂ) / (68427531025406090084114206210194860698867420966530903651647637598240241016422436782997504 : ℂ)) * Polynomial.X ^ 4)
def v00103 : UPoly := (Polynomial.C ((-113629050796609062526875361194864608872796736905805388338772891045556974459275 : ℂ) / (466320952173137799091741257136142754392281683623766158218635752521340901741545495113760768 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((214681599272587017308598042635516512345444077518717893823559325117388875467 : ℂ) / (58290119021642224886467657142017844299035210452970769777329469065167612717693186889220096 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-8704754035389819632568345053135110798271846017857744900165094985124559563 : ℂ) / (233160476086568899545870628568071377196140841811883079109317876260670450870772747556880384 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((235740304664915371520523442844841312242173575250721340906199269235856435157 : ℂ) / (29145059510821112443233828571008922149517605226485384888664734532583806358846593444610048 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-19063358445951989749872069814329812672805975677615830374355480207999833045 : ℂ) / (116580238043284449772935314284035688598070420905941539554658938130335225435386373778440192 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((970914163688190282548612834325122527077337515614069650881836915835486165 : ℂ) / (466320952173137799091741257136142754392281683623766158218635752521340901741545495113760768 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00103 : u00103*f+v00103*r00103=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00103, f, v00103, r00103, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00103 : IsCoprime f (spec a00103) :=
  coprime_of_modulo mod_a00103 bezout_00103

def u00105 : UPoly := (Polynomial.C ((4270052932561378370693634165642970284740894614742973476010320514385580915160123679820814522656207241281238146609 : ℂ) / (2732676833441223427495036772517484019160805693808453900759130905480435451744937684409084441197977925733307585134592 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((19443572223248698988741654503148744681401544021459119344593159430622935268083936190501986086572876014638966261 : ℂ) / (1366338416720611713747518386258742009580402846904226950379565452740217725872468842204542220598988962866653792567296 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((5666411357792588205032285649217746008658996602477866739095039369564804835579816287477415976960941995388625533 : ℂ) / (5465353666882446854990073545034968038321611387616907801518261810960870903489875368818168882395955851466615170269184 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-937794566386446881867331263050621104475207196823277438231142113138308301023069337156862428364790774014017649 : ℂ) / (21861414667529787419960294180139872153286445550467631206073047243843483613959501475272675529583823405866460681076736 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-75334028398140039129742969884067644398205682291469278798983364811938913324828340672438042837403784603773 : ℂ) / (151815379635623523749724265139860223286711427433802994486618383637801969541385426911615802288776551429628199174144 : ℂ)) * Polynomial.X ^ 4)
def v00105 : UPoly := (Polynomial.C ((10028659405090795273719987959156685208548584692278109157010764345588231006223634880563513190045121 : ℂ) / (539788016482216973332352942719503016130529519764632869285754252934407002813814851241300630360094405083122485952512 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((22953818755595048955406281178827714591965860143893203202137216614130633128725210207517085010559 : ℂ) / (67473502060277121666544117839937877016316189970579108660719281616800875351726856405162578795011800635390310744064 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((3670732055789218243573564173813657844184178526457475568970339542888862180891136722494671516033 : ℂ) / (269894008241108486666176471359751508065264759882316434642877126467203501406907425620650315180047202541561242976256 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-29069596408951333674814035351936657082127261655641228859861540773399429993366980444965169025631 : ℂ) / (33736751030138560833272058919968938508158094985289554330359640808400437675863428202581289397505900317695155372032 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-2945028948733820259480339732561177103121708487688286869349713043038786306544300297452834695585 : ℂ) / (134947004120554243333088235679875754032632379941158217321438563233601750703453712810325157590023601270780621488128 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-611676214399518487595642546038652925714670586250452189434124109035151312319883415492584168031 : ℂ) / (539788016482216973332352942719503016130529519764632869285754252934407002813814851241300630360094405083122485952512 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00105 : u00105*f+v00105*r00105=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00105, f, v00105, r00105, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00105 : IsCoprime f (spec a00105) :=
  coprime_of_modulo mod_a00105 bezout_00105

def u00106 : UPoly := 0
def v00106 : UPoly := (Polynomial.C ((-27 : ℂ) / (214327 : ℂ)) * Polynomial.X ^ 0)
lemma bezout_00106 : u00106*f+v00106*r00106=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00106, f, v00106, r00106, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00106 : IsCoprime f (spec a00106) :=
  coprime_of_modulo mod_a00106 bezout_00106

def u00123 : UPoly := (Polynomial.C ((8903653812060730557641936768092821065208731906986227054660937187128792013907852000143960221803084008390350430294076955611664923472205801027160927462189594720328106317329954790268270341835 : ℂ) / (1175392830876780157471308511911478244449603839071307998249604250043987481066017184574051258453899793069854685861618534068716768780036169176069600448456011524823793987166271930264289558921216 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((6452744050093341297593028509150831868892365104992278451663413924987592699562276525448139499940685641993029490460055309236059458621220975102621767980975337430626472510703579437127084763 : ℂ) / (293848207719195039367827127977869561112400959767826999562401062510996870266504296143512814613474948267463671465404633517179192195009042294017400112114002881205948496791567982566072389730304 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-2303713515221748600683862729330654147098538565192771837155925360931452990930403241995603672954197907797619371580839119449765020528311325888377090219227250095008065886630109689118010353 : ℂ) / (2350785661753560314942617023822956488899207678142615996499208500087974962132034369148102516907799586139709371723237068137433537560072338352139200896912023049647587974332543860528579117842432 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((216349776834378629291537030041942290235202629590893430136846958735674916246075197769825755193994036544581177731585954288944274709089057732951320954562285006577755440343379555203257708525 : ℂ) / (881544623157585118103481383933608683337202879303480998687203187532990610799512888430538443840424844802391014396213900551537576585027126882052200336342008643617845490374703947698217169190912 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((33115718006678487068952039057001111081082896760351869741501852765482659805431881510508366197213508880649306794143861480291425106845202571818474617516233916535181971502421241708218533005 : ℂ) / (3526178492630340472413925535734434733348811517213923994748812750131962443198051553722153775361699379209564057584855602206150306340108507528208801345368034574471381961498815790792868676763648 : ℂ)) * Polynomial.X ^ 4)
def v00123 : UPoly := (Polynomial.C ((6561250401584530548421954392358932857294982798393866136582069003241926675527586818968092268840438043990738029743071857835805104625794635491614569306993134607 : ℂ) / (2437851797374062548829380617297880803302882036592342514888068074165307368136924530968402610126606978218957866972245848438819964877112054587403615744945801681116017158567082522029637603688448 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-16590240140559812548679068474732830574422088413107952217913870764181318077549178088702424576792417217126204962047189073812445622646781236617726590637865039 : ℂ) / (304731474671757818603672577162235100412860254574042814361008509270663421017115566371050326265825872277369733371530731054852495609639006823425451968118225210139502144820885315253704700461056 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((14888484000372409131808167665107550174566224641840991809208912521599705579426313906067696217440039257721483866087382127714049153695766647921335555235825695823 : ℂ) / (1218925898687031274414690308648940401651441018296171257444034037082653684068462265484201305063303489109478933486122924219409982438556027293701807872472900840558008579283541261014818801844224 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-87837600862638958207666335609014550351515351082693202942870833892399011434338357665725578085446609003110846575159372684745021654971645224432920259361965521 : ℂ) / (152365737335878909301836288581117550206430127287021407180504254635331710508557783185525163132912936138684866685765365527426247804819503411712725984059112605069751072410442657626852350230528 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((1410334876911883845679956392150150734801796268187444805203573778615103938069524157687092284361995890728773348538873841209150320301451758167814988780996967 : ℂ) / (87066135620502233886763593474924314403674358449726518388859574077332406004890161820300093218807392079248495249008780301386427317039716235264414848033778631468429184234538661501058485846016 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((1180649821842967899080967232891624846794942840963078375992311731583522992099642674771726797059560655005494999956165788455606983079533869684843096155081703983 : ℂ) / (2437851797374062548829380617297880803302882036592342514888068074165307368136924530968402610126606978218957866972245848438819964877112054587403615744945801681116017158567082522029637603688448 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00123 : u00123*f+v00123*r00123=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00123, f, v00123, r00123, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00123 : IsCoprime f (spec a00123) :=
  coprime_of_modulo mod_a00123 bezout_00123

def u00124 : UPoly := (Polynomial.C ((8384268767372707934464428783746553533765413654202162177637814617077245876057010692272033554127232526281293959 : ℂ) / (2907337404332124559500427716698750497729198592359112365160541384640771417289706199940990046347146288132570626048 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-8401206833711318174722398270317744747526755167202975699084298630296185639212069295441461323652084413238787 : ℂ) / (121139058513838523312517821529114604072049941348296348548355891026698809053737758330874585264464428672190442752 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((7278820724387694024517329994048452671260707555715654248521372879098865995540937575877119332376274403889067 : ℂ) / (5814674808664249119000855433397500995458397184718224730321082769281542834579412399881980092694292576265141252096 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((276027580662778341233042775816121738768742152045841335338610334984640793911083575612407306237827907160897 : ℂ) / (5814674808664249119000855433397500995458397184718224730321082769281542834579412399881980092694292576265141252096 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((4448363585348672070747686528471013930194004238758234920395134684695774083923851185879367649783828945 : ℂ) / (107679163123412020722238063581435203619599947865152309820760792023732274714433562960777409123968381041947060224 : ℂ)) * Polynomial.X ^ 4)
def v00124 : UPoly := (Polynomial.C ((519555321311438194615379595011067857880729215013271645540397593656859570451099987196723244404921 : ℂ) / (861433304987296165777904508651481628956799582921218478566086336189858197715468503686219272991747048335576481792 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1416847725733573775063289357071512063330820613946897692525967858068360629388887636898143444025 : ℂ) / (107679163123412020722238063581435203619599947865152309820760792023732274714433562960777409123968381041947060224 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((77969811686065568887314141465684606061226055447711019267036408109967316506671894884146616185 : ℂ) / (430716652493648082888952254325740814478399791460609239283043168094929098857734251843109636495873524167788240896 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-2372142097690985449551906443370286193185363405643575828881659392298564603244832218604354324743 : ℂ) / (53839581561706010361119031790717601809799973932576154910380396011866137357216781480388704561984190520973530112 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((380200972896102092018285399517427348429961386640896436086495063175237569620028707413674504167 : ℂ) / (215358326246824041444476127162870407239199895730304619641521584047464549428867125921554818247936762083894120448 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-40315925333377932439829523812684940619704313674299128147792204687401586351454426185367687271 : ℂ) / (861433304987296165777904508651481628956799582921218478566086336189858197715468503686219272991747048335576481792 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00124 : u00124*f+v00124*r00124=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00124, f, v00124, r00124, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00124 : IsCoprime f (spec a00124) :=
  coprime_of_modulo mod_a00124 bezout_00124

def u00134 : UPoly := (Polynomial.C ((49155155659661445019969223287407897441355907819436685696670909159937074872580823645178727739109775410305600014311328821 : ℂ) / (10100627523312664103743893275072369916106860381629605426039365651259561311804322105601924997615192199232609301390384168960 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-2007430642633006062699525620604898478032917962047349756330879716659021976108965279540625019257402979663256731903156663 : ℂ) / (40402510093250656414975573100289479664427441526518421704157462605038245247217288422407699990460768796930437205561536675840 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((3873729975594046737200185105558120609651169621055073567132203607948698943543561464151563244138103062057841090740327 : ℂ) / (10100627523312664103743893275072369916106860381629605426039365651259561311804322105601924997615192199232609301390384168960 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((3429095518467606801654402184234369055662105118109009191250198407620864605587328452497980016030204539787568797348003 : ℂ) / (40402510093250656414975573100289479664427441526518421704157462605038245247217288422407699990460768796930437205561536675840 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((478531587379962593134375103527410043268578554833308898324226245629587756718982056598818143085448073675611473736449 : ℂ) / (161610040373002625659902292401157918657709766106073686816629850420152980988869153689630799961843075187721748822246146703360 : ℂ)) * Polynomial.X ^ 4)
def v00134 : UPoly := (Polynomial.C ((368550152087817205416771105002046461397871625361471898786484107313562361783410465735492117441923488097 : ℂ) / (2074993110962009020818498569101286856839730330250822645546852400456285188005233578237234962473046891299143441668345587302400 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-1714484642195210579020723324566100553498247561770423284699268010782169371715515255318803094199062817 : ℂ) / (259374138870251127602312321137660857104966291281352830693356550057035648500654197279654370309130861412392930208543198412800 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((146631507744218981762303350765936694031386990393841726117660085922783932486037133572266551751527713 : ℂ) / (1037496555481004510409249284550643428419865165125411322773426200228142594002616789118617481236523445649571720834172793651200 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-3019180160571227245143981176265030896293113167981113129443593237262048935585675120727884637823042239 : ℂ) / (129687069435125563801156160568830428552483145640676415346678275028517824250327098639827185154565430706196465104271599206400 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((550036137181291488246480847401030972147771924129742543533346288615359655460259740904462800404580031 : ℂ) / (518748277740502255204624642275321714209932582562705661386713100114071297001308394559308740618261722824785860417086396825600 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-56336432097451724006193015435222829357383742565428137925104961415252327733210267261087000679090879 : ℂ) / (2074993110962009020818498569101286856839730330250822645546852400456285188005233578237234962473046891299143441668345587302400 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_00134 : u00134*f+v00134*r00134=1 := by
  apply Polynomial.funext
  intro x
  simp only [u00134, f, v00134, r00134, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a00134 : IsCoprime f (spec a00134) :=
  coprime_of_modulo mod_a00134 bezout_00134

def u07867 : UPoly := (Polynomial.C ((174408371526839530793503167276310719585119762175171193134696842986629060039884354766574399080382005231003489095023708847982267468613507313900529461615538777164432993163555261257 : ℂ) / (27269590714651917988636726520542942015861623624995926172129488011155993575498392401566395821617971352514505661769620591873742371079584168486882938263121770977144502768010749018112 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-253794788350214142774980207117426178518100571355159858313983065660133107695067391734432290453267733953977380650384217238316160571295001887361437538444004227954486064274640463 : ℂ) / (3408698839331489748579590815067867751982702953124490771516186001394499196937299050195799477702246419064313207721202573984217796384948021060860367282890221372143062846001343627264 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((10367329161946481630238996445505430373959339402768142228423006616242936115097202126127160421341023168467308705248459186435044172345994668683697046824546187278602702643247727 : ℂ) / (13634795357325958994318363260271471007930811812497963086064744005577996787749196200783197910808985676257252830884810295936871185539792084243441469131560885488572251384005374509056 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((351686822225903235610232057209733493997104434577401116279184423544803987234838381406131491476186873722421178722996819695504913886956898380178759788770793550395478227071419 : ℂ) / (1704349419665744874289795407533933875991351476562245385758093000697249598468649525097899738851123209532156603860601286992108898192474010530430183641445110686071531423000671813632 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((62404874134614729538379160337911790397314903214245304988546956838772471761466068077811236760500830922986207808011565030571773269904570117869886839266605203443035112640837 : ℂ) / (6817397678662979497159181630135735503965405906248981543032372002788998393874598100391598955404492838128626415442405147968435592769896042121720734565780442744286125692002687254528 : ℂ)) * Polynomial.X ^ 4)
def v07867 : UPoly := (Polynomial.C ((-16034299745548165935612938268546985067263750120512330868183371189997618920838640598191394956665895449605757716860801351625299632838351347620450017813 : ℂ) / (64138077360861311109273580776316999621306538765990418356848555802238896889572218928484162972445468621114117316482147632087042056779181964281148670794862405338243870510361281690599424 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((23748786645949478138582570465562331153415722695504972918265999465456716725361150768540615703089118520613845703687137802897798113767366438277817415 : ℂ) / (2672419890035887962886399199013208317554439115249600764868689825093287370398842455353506790518561192546421554853422818003626752365799248511714527949785933555760161271265053403774976 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-4308669681457228376287497815294839679813871903556853416233843760500916924491099150085063454337542020691307990141576811218062207970753563679365333 : ℂ) / (32069038680430655554636790388158499810653269382995209178424277901119448444786109464242081486222734310557058658241073816043521028389590982140574335397431202669121935255180640845299712 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((563326536656400134288571573040170782535715225932365392648258761552540331159895772090727072063463938351175740223158952890471239346647484941784675 : ℂ) / (9089863571550639329545575506847647338620541208331975390709829337051997858499464133855465273872657117504835220589873530624580790359861389495627646087707256992381500922670249672704 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-18453824354182156157786349119708993611554446812380060558390530806269211652834450941374300481212715445472563054201492484736775887029758473214441177 : ℂ) / (5344839780071775925772798398026416635108878230499201529737379650186574740797684910707013581037122385092843109706845636007253504731598497023429055899571867111520322542530106807549952 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((6997560656486636144714847302879995964437854712465202736075392522803901115261986524190374989354404478488168579320592039810316198963815820073236619 : ℂ) / (64138077360861311109273580776316999621306538765990418356848555802238896889572218928484162972445468621114117316482147632087042056779181964281148670794862405338243870510361281690599424 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_07867 : u07867*f+v07867*r07867=1 := by
  apply Polynomial.funext
  intro x
  simp only [u07867, f, v07867, r07867, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a07867 : IsCoprime f (spec a07867) :=
  coprime_of_modulo mod_a07867 bezout_07867

def u07942 : UPoly := (Polynomial.C ((577559420927639924157475519485893202460680128144497731284349269238108374409213397755025374485327984408822625884042866718955666904956244754558038329621923967676896439949764380854672127474887019400198491407374432835608115432078069249235832112638416007955056810790722606876111177466854093818029874169334298006989764628642064247682976583190288230075934111236368398881562419303624326350935798637418335576452769475366142937511314915244199722683675658545855450062019237984159882452550554061341174974275212776121 : ℂ) / (74503479680488290114635211178649167020398079855905091556615456449366283136824896340570274068328348231486217032420834197190169590981831333355818583948679184837872670849025868328127315074213177383887209141245466757034628560826450572279637811710650169379246089434612057247381523134421183561769678382528455781111248985312844072219066143360606108331230843981523021844626220560630501848196729651606381837555257916386568029539153894427912353574525802437191678062707586287983910519884785122886327405542939188789248 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-274527710385108156287356663768434261174362398891525165016369108263781840922992562044743783911561195814779440357871245423842645148332531329519964041683332097032169968137795577021097677114432569538583946060110773227595271066317804833563863243136529525873870070257205724054361791905507563805296779078271856251132130770892962666337197500425086576061994881866358650391875674866319677943872641979808488897283514413323506621020265546722342418151509179609142754999164192116130827704076251657250318470794525719 : ℂ) / (37251739840244145057317605589324583510199039927952545778307728224683141568412448170285137034164174115743108516210417098595084795490915666677909291974339592418936335424512934164063657537106588691943604570622733378517314280413225286139818905855325084689623044717306028623690761567210591780884839191264227890555624492656422036109533071680303054165615421990761510922313110280315250924098364825803190918777628958193284014769576947213956176787262901218595839031353793143991955259942392561443163702771469594394624 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1617882892065080493975361501371365847708050837819279600931750747955686793752060085031695195471447470999003741374550728414230710152378183201300598923353596931045014118022477415334332156457227233736768235462308895676810036961914483601426999417539471013057610103935826348287309463871223442796718428592750428890891851455352858574206645068288316820359845865397225273894905576934428444676728978749781447036138310763611974827505627361826124452679867024067291132462703135682570223792788697195459204550956336971 : ℂ) / (8278164408943143346070579019849907446710897761767232395179495161040698126313877371174474896480927581276246336935648244132241065664647925928424287105408798315319185649891763147569701674912575264876356571249496306337180951202938952475515312412294463264360676603845784138597947014935687062418853153614272864567916553923649341357674015928956234259025649331280335760514024506736722427577414405734042426395028657376285336615461543825323594841613978048576853118078620698664878946653865013654036378393659909865472 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-3340214883112433592737149458687896245708747334485098228459208998930229666247718740086759006117307667870546016018331262078475063702419598372283320015874367957002832409292381512587003831029331278400681837701702993890893193240182333957803876860867291160971449718067106256242907224256007370811292105065343358955423327895945927556439898134576141739916393598346954679945444210753040349635098973897340251779825533904144706714189297755213775937165695187717231340175225931202839138229628413637160148976060254127 : ℂ) / (24834493226829430038211737059549722340132693285301697185538485483122094378941632113523424689442782743828739010806944732396723196993943777785272861316226394945957556949675289442709105024737725794629069713748488919011542853608816857426545937236883389793082029811537352415793841044807061187256559460842818593703749661770948024073022047786868702777076947993841007281542073520210167282732243217202127279185085972128856009846384631475970784524841934145730559354235862095994636839961595040962109135180979729596416 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-4026364623883449871137281850983228173823250670358501436314449048942720628160147781121582654907721945262103352149016228474679711848108937147223803282032685571271394804492571242149663314592685435761432141894986596794725390054021083960588702713580112827623861368737674434969053328786084453837857456444648538496894212504366606879361794840806108888974184641417542417382018873052152517840798951250022154690259259014184617712727120854476844746417789635557026401111542290056058635948355445334305970756046408859 : ℂ) / (74503479680488290114635211178649167020398079855905091556615456449366283136824896340570274068328348231486217032420834197190169590981831333355818583948679184837872670849025868328127315074213177383887209141245466757034628560826450572279637811710650169379246089434612057247381523134421183561769678382528455781111248985312844072219066143360606108331230843981523021844626220560630501848196729651606381837555257916386568029539153894427912353574525802437191678062707586287983910519884785122886327405542939188789248 : ℂ)) * Polynomial.X ^ 4)
def v07942 : UPoly := (Polynomial.C ((-1530924010501232921070386943508114788318548173233718763688869455527272925202412853386317551804329736905434928199789120569039168703239799716677927580404898261511710755314497232944117650649270418907110804918941467806000292469371708195024559236079454448965556537487239762707173794144292573674105845880781094573043997204391342133163345496119118744141478303987070259307388824922693665554937433466312690047593761038636685350542227573123 : ℂ) / (29917957363441617008256459909264148747465209513926383310721709371771345630063662966293520193625640017473256503832651103968734204524010714652734832021725028077077115747484049944074025384089859382107170554511893681317844636290445605116750128385762416625091777423808569430907515929969362389521981870283909501060529629609313055666772884199335082951908187464118451936769389572555192201401941431181852815746424375273632872743254433908294957286604150428207901409879877229423353853809180661680758224512448614610605556982675268435968 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((18687896308742809427157433235600895325767377897151376485426085888024352437382651319766219284734431414156759122345277906031282677131178811455505220052266143016782044109490067572522395637446702507353432407704880429646100590055546771726907586702096197379190923204854493183025603765256550697953647746363884589251386909613769437836843935553376625893757697189730126024386398126323441686970877447197913530955634599547121066994728163523 : ℂ) / (3739744670430202126032057488658018593433151189240797913840213671471418203757957870786690024203205002184157062979081387996091775565501339331591854002715628509634639468435506243009253173011232422763396319313986710164730579536305700639593766048220302078136472177976071178863439491246170298690247733785488687632566203701164131958346610524916885368988523433014806492096173696569399025175242678897731601968303046909204109092906804238536869660825518803525987676234984653677919231726147582710094778064056076826325694622834408554496 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((130190674970574674002852827737401967205531789181221444873092056016374725519805472242566606178463985667233120205214847638282312011715716610643035015088355437905484551346565413337700839401861918668156802643428516135400680170027378888790878775179946580973266586561065601969552075705179928423153174090213162497261036455266016128929528620423747584461499118913985342090711716437895213332889924917396489762961772932817210931096125577627 : ℂ) / (2136996954531544072018318564947439196247514965280455950765836383697953259290261640449537156687545715533804035988046507426338157466000765332338202287266073434076936839106003567433858956006418527293369325322278120094131759735031828936910723456125886901792269815986326387921965423569240170680141562163136392932894973543522361119055206014238220210850584818865603709769242112325370871528710102227275201124744598233830919481661030993449639806186010744871992957848562659244525275272084332977197016036603472472186111213048233459712 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((-32445457155663270060214619878052321676154562244042141543924089001520200205634082381655892931166886665816416297573323910683374256632097754146802134320564662446683384405292386005620064520334184013952432654148521628934406393087575683719425641396640360974715780280252620950406064528981052295022749530231763755529723649528580969230064105581039939564793905306696031842543735251508716822584295102815860498167087993907240841985613629731 : ℂ) / (1869872335215101063016028744329009296716575594620398956920106835735709101878978935393345012101602501092078531489540693998045887782750669665795927001357814254817319734217753121504626586505616211381698159656993355082365289768152850319796883024110151039068236088988035589431719745623085149345123866892744343816283101850582065979173305262458442684494261716507403246048086848284699512587621339448865800984151523454602054546453402119268434830412759401762993838117492326838959615863073791355047389032028038413162847311417204277248 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((18985193733975681070390725500192717058439926086128205657405324029952202854225931765745234548796028468512291741137875737763117379151932557307742428336072750943579709779523234473228755537855088369782225501716443514506296277768371240638586199503679959869878158659262306636933426365608975949923755037438091771924559554857920904994290367006353514841697481960527515977513201617523396176447747287117880910770077773524442256169596878115 : ℂ) / (7479489340860404252064114977316037186866302378481595827680427342942836407515915741573380048406410004368314125958162775992183551131002678663183708005431257019269278936871012486018506346022464845526792638627973420329461159072611401279187532096440604156272944355952142357726878982492340597380495467570977375265132407402328263916693221049833770737977046866029612984192347393138798050350485357795463203936606093818408218185813608477073739321651037607051975352469969307355838463452295165420189556128112153652651389245668817108992 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((-7875804366735534319896344098739408161543016860925525190765455742239867884511080750194804831890269537857843444825714706702350381272416877831568698717589218729764356002099235586793957001961057407157485684697763565924244533709744981041486331107101887694090418863899805062584389079664693147800935698421405201272280376084373215933441923621492471351418138315072663655961805837682841285490071259932831479251655163104946531054187333381 : ℂ) / (4273993909063088144036637129894878392495029930560911901531672767395906518580523280899074313375091431067608071976093014852676314932001530664676404574532146868153873678212007134867717912012837054586738650644556240188263519470063657873821446912251773803584539631972652775843930847138480341360283124326272785865789947087044722238110412028476440421701169637731207419538484224650741743057420204454550402249489196467661838963322061986899279612372021489743985915697125318489050550544168665954394032073206944944372222426096466919424 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_07942 : u07942*f+v07942*r07942=1 := by
  apply Polynomial.funext
  intro x
  simp only [u07942, f, v07942, r07942, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a07942 : IsCoprime f (spec a07942) :=
  coprime_of_modulo mod_a07942 bezout_07942

def u07947 : UPoly := 0
def v07947 : UPoly := (Polynomial.C ((-3 : ℂ) / (7 : ℂ)) * Polynomial.X ^ 0)
lemma bezout_07947 : u07947*f+v07947*r07947=1 := by
  apply Polynomial.funext
  intro x
  simp only [u07947, f, v07947, r07947, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a07947 : IsCoprime f (spec a07947) :=
  coprime_of_modulo mod_a07947 bezout_07947

def u07960 : UPoly := (Polynomial.C ((97690568004227077736819973606422920282250207533194806169134458971698895505887182588667128671278165806691119081 : ℂ) / (25977175996349330203003249489225289695298161665983228663646123881873661875397668719527178464891432265813579530240 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((-221259520649650396496075048799329752375859868123321054211474476113117807674165076531106454042560176158089383 : ℂ) / (6112276705023371812471352820994185810658390980231347920857911501617332205975922051653453756445042886073783418880 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((2037433446775610296406457109115317399745338189598673729397821188666999268040591431981900302216158460568217 : ℂ) / (6494293999087332550750812372306322423824540416495807165911530970468415468849417179881794616222858066453394882560 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((587039267320685332085432904586229669469244692728312148338711634369771795759783738283397349205025936302501 : ℂ) / (8659058665449776734334416496408429898432720555327742887882041293957887291799222906509059488297144088604526510080 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((245627288858836357789752554975140344600345340865978589598943337125372503552249608288239998734356730182983 : ℂ) / (103908703985397320812012997956901158781192646663932914654584495527494647501590674878108713859565729063254318120960 : ℂ)) * Polynomial.X ^ 4)
def v07960 : UPoly := (Polynomial.C ((-4349825128372091109026241524223164874985515747575172753257110024761763249150614695902030109381 : ℂ) / (61575528287642856777489183974459945944410457282330616091605626979256087408350029557397756361224135741187744071680 : ℂ)) * Polynomial.X ^ 0) + (Polynomial.C ((7094525258382321598231503916550666121455754647917579168159720441653627607442726210274344407 : ℂ) / (2565647011985119032395382665602497747683769053430442337150234457469003642014584564891573181717672322549489336320 : ℂ)) * Polynomial.X ^ 1) + (Polynomial.C ((-1922096013604298723231638606653484106383208899985652418841933967550042936754954467426575749 : ℂ) / (30787764143821428388744591987229972972205228641165308045802813489628043704175014778698878180612067870593872035840 : ℂ)) * Polynomial.X ^ 2) + (Polynomial.C ((2846020438091303177367442669789822694275881030683189881540831808664636027890528144932696003 : ℂ) / (427607835330853172065897110933749624613961508905073722858372409578167273669097427481928863619612053758248222720 : ℂ)) * Polynomial.X ^ 3) + (Polynomial.C ((-1552632930955223810765615596643470341985977110802004289430943165417661796762800299755613001 : ℂ) / (5131294023970238064790765331204995495367538106860884674300468914938007284029169129783146363435344645098978672640 : ℂ)) * Polynomial.X ^ 4) + (Polynomial.C ((483350388027553433494762733130059042000433047799186261023080220206246508577936562837067227 : ℂ) / (61575528287642856777489183974459945944410457282330616091605626979256087408350029557397756361224135741187744071680 : ℂ)) * Polynomial.X ^ 5)
lemma bezout_07960 : u07960*f+v07960*r07960=1 := by
  apply Polynomial.funext
  intro x
  simp only [u07960, f, v07960, r07960, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num <;> ring
lemma coprime_a07960 : IsCoprime f (spec a07960) :=
  coprime_of_modulo mod_a07960 bezout_07960

theorem specialized_baseD_coprime : IsCoprime f (spec baseD) := by
  unfold baseD
  simp only [map_mul, map_pow, spec_C]
  norm_num only [div_one, Polynomial.C_1, one_mul]
  exact (((((((((((((((((((((coprime_power coprime_a00012 1).mul_right (coprime_power coprime_a00013 2)).mul_right (coprime_power coprime_a00014 10)).mul_right (coprime_power coprime_a00015 2)).mul_right (coprime_power coprime_a00018 2)).mul_right (coprime_power coprime_a00026 1)).mul_right (coprime_power coprime_a00033 1)).mul_right (coprime_power coprime_a00034 3)).mul_right (coprime_power coprime_a00042 5)).mul_right (coprime_power coprime_a00100 5)).mul_right (coprime_power coprime_a00101 7)).mul_right (coprime_power coprime_a00103 7)).mul_right (coprime_power coprime_a00105 4)).mul_right (coprime_power coprime_a00106 2)).mul_right (coprime_power coprime_a00123 4)).mul_right (coprime_power coprime_a00124 6)).mul_right (coprime_power coprime_a00134 11)).mul_right (coprime_power coprime_a07867 1)).mul_right (coprime_power coprime_a07942 1)).mul_right (coprime_power coprime_a07947 1)).mul_right (coprime_power coprime_a07960 2))

abbrev Coeff := MvPolynomial (Fin 5) ℂ

def equation : Polynomial Coeff :=
  Polynomial.X^6 +
    (Polynomial.C (MvPolynomial.C (1/2) * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3) * Polynomial.X^3 +
    Polynomial.C (MvPolynomial.C (1/2) * MvPolynomial.X 1^3 * MvPolynomial.X 2 * MvPolynomial.X 4) * Polynomial.X +
    Polynomial.C ((MvPolynomial.X 0)^6 + (MvPolynomial.X 1)^6 + (MvPolynomial.X 2)^6 +
      (MvPolynomial.X 3)^6 + (MvPolynomial.X 4)^6 +
      MvPolynomial.C (1/2) * MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4))

lemma equation_monic : equation.Monic := by
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 3 _) (by decide)
    · simpa using lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 1 _) (by decide : (1 : WithBot ℕ) < 6)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

lemma originalF_univariate :
    MvPolynomial.finSuccEquiv ℂ 5 CycleQ2Workspace.originalF = equation := by
  have he : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [CycleQ2Workspace.originalF,HodgeSubmission.F,equation,MvPolynomial.finSuccEquiv_apply,he]
  ring

def coefficientSpec : Coeff →+* ℂ := MvPolynomial.eval ![1,1,2,2,1]

lemma mapped_univariate (P : CycleQ2Concrete.Poly) :
    (MvPolynomial.finSuccEquiv ℂ 5 P).map coefficientSpec = spec P := by
  have he : (Fin.cases (Polynomial.X : Polynomial Coeff) (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X,Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3),Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply,coefficientSpec,spec]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.map_mul,hp,map_mul]
    congr 1
    fin_cases i <;> simp [MvPolynomial.finSuccEquiv_apply,he,coefficientSpec,spec,specVars,Polynomial.C_ofNat]

lemma ambient_relPrime_of_specialization (D : CycleQ2Concrete.Poly)
    (h : IsRelPrime f (spec D)) : IsRelPrime CycleQ2Workspace.originalF D := by
  apply IsRelPrime.of_map (MvPolynomial.finSuccEquiv ℂ 5)
  apply HodgeComputer.relPrime_of_specialization coefficientSpec
  · rw [originalF_univariate]
    rw [equation_monic]
    exact isUnit_one
  · rw [mapped_univariate,mapped_univariate,specialized_originalF]
    exact h

lemma f_not_isUnit : ¬ IsUnit f := by
  intro h
  have hc := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit h)
  have h6 := congrArg (fun p : UPoly => p.coeff 6) hc
  norm_num [f,Polynomial.coeff_X] at h6


/-- Complex coprimality of the actual denominator, without dense expansion. -/
theorem baseD_legal : IsRelPrime CycleQ2Workspace.originalF baseD :=
  ambient_relPrime_of_specialization baseD specialized_baseD_coprime.isRelPrime

/-- The specialized Bezout certificate also rules out the zero denominator. -/
theorem baseD_ne_zero : baseD ≠ 0 := by
  intro hz
  have h := specialized_baseD_coprime
  rw [hz, map_zero] at h
  exact f_not_isUnit (isCoprime_zero_right.mp h)

#print axioms baseD_legal
#print axioms baseD_ne_zero

#print axioms specialized_originalF
#print axioms specialized_baseD_coprime
end CycleQ2Concrete.Denominator
