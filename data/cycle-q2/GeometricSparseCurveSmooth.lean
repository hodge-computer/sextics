import Proposal.GeometricAdjunctionOverlap
import Proposal.GeometricCofactorResidue
import Proposal.GeometricAffineOverlap

/-!
# Nonsingularity of the actual sparse curve at a cube root of two

The first affine chart is trigonal after eliminating its quadratic equation.
Its discriminant is a degree-twelve Gaussian polynomial independent of the
choice of cube root. An explicit integer Gaussian Bezout identity proves
that this discriminant and its derivative have no common zero. The identity
is verified by the Lean kernel through ordinary polynomial normalization.
The later gradient criterion concerns the literal affine chart equations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricSparseCurveSmooth

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAdjunctionOverlap
  CycleQ2GeometricCofactorResidue

variable {K : Type*} [Field K] [CharZero K]

def discriminant (i a : K) : K :=
  54 * i * a ^ 12 - 8 * a ^ 9 - 24 * a ^ 8 +
    (-132 + 108 * i) * a ^ 7 + (100 + 108 * i) * a ^ 6 -
    108 * a ^ 2 + 216 * i * a + 108

def discriminantDerivative (i a : K) : K :=
  648 * i * a ^ 11 - 72 * a ^ 8 - 192 * a ^ 7 +
    (-924 + 756 * i) * a ^ 6 + (600 + 648 * i) * a ^ 5 -
    216 * a + 216 * i

private def bezoutLeft (i a : K) : K :=
  (((((((((((-1568473745149695422139240910549766472 + (-153231924470599895231887789748756904) * i) * a +
    (-1623586281210574736349378035556336168 + (635964004344987789739807116210758424) * i)) * a +
    (2008976675220842397872946006288673008 + (-3834969905375063249391048688402037544) * i)) * a +
    (247601995693483137444702634242546108 + (3877491846275673815744061944815833156) * i)) * a +
    (-31925439919978932615230913482369232 + (-2042989086378542393183196895769386224) * i)) * a +
    (-3978918360340144044878095178230858740 + (-2442727156742053700502704726418102180) * i)) * a +
    (313233183231193939161925501039117668 + (-104831240669201806774431513365001924) * i)) * a +
    (925180517899290792140318156040354492 + (303964797906926195288135329876222044) * i)) * a +
    (-1143732505870275629814734543431189452 + (673958323832631628258552375839458736) * i)) * a +
    (267848555733887640494424195809051712 + (-609065609912517471482221292046193416) * i)) * a +
    (-220450623081917329056567394538691804 + (-885016123180572654631636736629739328) * i))

private def bezoutRight (i a : K) : K :=
  ((((((((((((130706145429141285178270075879147206 + (12769327039216657935990649145729742) * i) * a +
    (135298856767547894695781502963028014 + (-52997000362082315811650593017563202) * i)) * a +
    (-167414722935070199822745500524056084 + (319580825447921937449254057366836462) * i)) * a +
    (-21106437679613100636539688007091055 + (-318283352173745362972069233331721385) * i)) * a +
    (2731553037969195646368798213702778 + (194624032697623460002631660072619846) * i)) * a +
    (423507602420109342594236900796151583 + (361172061647722309298284549563861231) * i)) * a +
    (248314450048263093843543126302571214 + (-31392556980340710300010282439768802) * i)) * a +
    (-410174638615044492682943321337676284 + (-110627810090945074493003985373898688) * i)) * a +
    (535145856734753663693198677732830204 + (125611097033329581940882890100447878) * i)) * a +
    (-470903439783259634376488285824255224 + (-152071445225800132736357554737151518) * i)) * a +
    (299496113744138453839495272337096110 + (576432339457230147563030466219395520) * i)) * a +
    (442508061590286327315818368314869664 + (-225487314294037610958182768224692402) * i))

/-- Exact polynomial identity, valid in every characteristic-zero field
with an element whose square is minus one. -/
theorem discriminant_bezout (i a : K) (hi : i ^ 2 = -1) :
    bezoutLeft i a * discriminant i a +
      bezoutRight i a * discriminantDerivative i a = 24896592594665052428858199326354844000 := by
  unfold bezoutLeft bezoutRight discriminant discriminantDerivative
  ring_nf
  simp only [hi]
  ring

def trigonalP (r a : K) : K := r ^ 2 * a ^ 2 * (a + 1)
def trigonalQ (i a : K) : K := (1 - i) * a ^ 6 + 2 * a - 2 * i
def trigonalPDerivative (r a : K) : K := r ^ 2 * (3 * a ^ 2 + 2 * a)
def trigonalQDerivative (i a : K) : K := 6 * (1 - i) * a ^ 5 + 2

private theorem sixth_power (r : K) (hr : r ^ 3 = 2) : r ^ 6 = 4 := by
  calc
    r ^ 6 = (r ^ 3) ^ 2 := by ring
    _ = 4 := by rw [hr]; norm_num

theorem discriminant_eq (i r a : K) (hi : i ^ 2 = -1) (hr : r ^ 3 = 2) :
    discriminant i a = -2 * trigonalP r a ^ 3 - 27 * trigonalQ i a ^ 2 := by
  unfold discriminant trigonalP trigonalQ
  ring_nf
  simp only [hi, sixth_power r hr]
  ring

theorem discriminantDerivative_eq (i r a : K)
    (hi : i ^ 2 = -1) (hr : r ^ 3 = 2) :
    discriminantDerivative i a =
      -6 * trigonalP r a ^ 2 * trigonalPDerivative r a -
        54 * trigonalQ i a * trigonalQDerivative i a := by
  unfold discriminantDerivative trigonalP trigonalQ trigonalPDerivative trigonalQDerivative
  ring_nf
  simp only [hi, sixth_power r hr]
  ring

/-- The actual trigonal equation cannot vanish together with its two
partial derivatives; the coefficient r is any cube root of two. -/
theorem trigonal_no_critical_point (i r a b : K)
    (hi : i ^ 2 = -1) (hr : r ^ 3 = 2)
    (h : 2 * b ^ 3 + trigonalP r a * b + trigonalQ i a = 0)
    (hb : 6 * b ^ 2 + trigonalP r a = 0)
    (ha : trigonalPDerivative r a * b + trigonalQDerivative i a = 0) : False := by
  have hp : trigonalP r a = -6 * b ^ 2 := by linear_combination hb
  have hq : trigonalQ i a = 4 * b ^ 3 := by linear_combination h - b * hb
  have hqa : trigonalQDerivative i a = -trigonalPDerivative r a * b := by
    linear_combination ha
  have hd : discriminant i a = 0 := by
    rw [discriminant_eq i r a hi hr, hp, hq]
    ring
  have hda : discriminantDerivative i a = 0 := by
    rw [discriminantDerivative_eq i r a hi hr, hp, hq, hqa]
    ring
  have hc := discriminant_bezout i a hi
  rw [hd, hda, mul_zero, mul_zero, add_zero] at hc
  norm_num at hc

/-- On the actual first affine chart, the two equation gradients are
independent at every field-valued point of the sparse curve. -/
theorem first_chart_jacobian_nonzero (i r a b c : K)
    (hi : i ^ 2 = -1) (hr : r ^ 3 = 2)
    (hf : quadricOne r a b c = 0) (hh : cubicOne i 0 a b c = 0) :
    ∃ j : Fin 3, cofactor (gradQuadricOne r a) (gradCubicOne i 0 a b c) j ≠ 0 := by
  by_contra! hz
  have hr0 : r ≠ 0 := by
    intro h
    norm_num [h] at hr
  have ha2 : a ^ 2 = r * c :=
    sub_eq_zero.mp (by simpa only [quadricOne] using hf)
  have hra2 : r ^ 2 * a ^ 2 = 2 * c := by
    rw [ha2]
    calc
      r ^ 2 * (r * c) = r ^ 3 * c := by ring
      _ = 2 * c := by rw [hr]
  have ha6 : a ^ 6 = 2 * c ^ 3 := by
    calc
      a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = (r * c) ^ 3 := by rw [ha2]
      _ = 2 * c ^ 3 := by rw [mul_pow, hr]
  have hra5 : r * a ^ 5 = 2 * a * c ^ 2 := by
    calc
      r * a ^ 5 = r * a * (a ^ 2) ^ 2 := by ring
      _ = r * a * (r * c) ^ 2 := by rw [ha2]
      _ = r ^ 3 * a * c ^ 2 := by ring
      _ = 2 * a * c ^ 2 := by rw [hr]
  have h0 : r * (3 * b ^ 2 + c + a * c) = 0 := by
    simpa [cofactor, gradQuadricOne, gradCubicOne] using hz 0
  have hB : 3 * b ^ 2 + c + a * c = 0 :=
    (mul_eq_zero.mp h0).resolve_left hr0
  have h1 : -r * (b * c + 1) -
      (2 * a) * (3 * (1 - i) * c ^ 2 + b + a * b) = 0 := by
    simpa [cofactor, gradQuadricOne, gradCubicOne] using hz 1
  have hA : r * (b * c + 1) +
      2 * a * (3 * (1 - i) * c ^ 2 + b + a * b) = 0 := by
    linear_combination -h1
  have h : 2 * b ^ 3 + trigonalP r a * b + trigonalQ i a = 0 := by
    unfold trigonalP trigonalQ
    dsimp [cubicOne] at hh
    linear_combination 2 * hh + (a + 1) * b * hra2 + (1 - i) * ha6
  have hb : 6 * b ^ 2 + trigonalP r a = 0 := by
    unfold trigonalP
    linear_combination 2 * hB + (a + 1) * hra2
  have hra : r * (trigonalPDerivative r a * b + trigonalQDerivative i a) = 0 := by
    unfold trigonalPDerivative trigonalQDerivative
    linear_combination 2 * hA + (3 * a ^ 2 + 2 * a) * b * hr +
      2 * b * ha2 + 6 * (1 - i) * hra5
  exact trigonal_no_critical_point i r a b hi hr h hb
    ((mul_eq_zero.mp hra).resolve_left hr0)

/-- The second affine chart has no singular field-valued points either.
On its overlap with the first chart this follows from the actual cofactor
transformation. At the remaining points a single literal minor is nonzero. -/
theorem second_chart_jacobian_nonzero (i r a b c : K)
    (hi : i ^ 2 = -1) (hr : r ^ 3 = 2)
    (hf : quadricTwo r a b c = 0) (hh : cubicTwo i 0 a b c = 0) :
    ∃ j : Fin 3, cofactor (gradQuadricTwo r a b c) (gradCubicTwo i 0 a b c) j ≠ 0 := by
  have hr0 : r ≠ 0 := by
    intro h
    norm_num [h] at hr
  by_cases hb : b = 0
  · have ha2 : a ^ 2 = 0 := by simpa [quadricTwo, hb] using hf
    have ha : a = 0 := eq_zero_of_pow_eq_zero ha2
    have hc : c ≠ 0 := by
      intro hc
      norm_num [cubicTwo, ha, hb, hc] at hh
    have hi1 : 1 - i ≠ 0 := by
      intro heq
      have heq' : i = 1 := (sub_eq_zero.mp heq).symm
      norm_num [heq'] at hi
    refine ⟨0, ?_⟩
    simpa [cofactor, gradQuadricTwo, gradCubicTwo, ha, hb, mul_assoc] using
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hr0) hc)
        (mul_ne_zero (mul_ne_zero (by norm_num : (3 : K) ≠ 0) hi1) (pow_ne_zero 2 hc))
  · let A := a * b⁻¹
    let B := b⁻¹
    let C := c * b⁻¹
    have hAb : A * b = a := by
      dsimp [A]
      rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
    have hCb : C * b = c := by
      dsimp [C]
      rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
    have hBb : B * b = 1 := inv_mul_cancel₀ hb
    have hfirstF : quadricOne r A B C = 0 := by
      have hs := quadratic_scaling r A C b
      rw [hAb, hCb, hf] at hs
      exact (mul_eq_zero.mp hs.symm).resolve_left (pow_ne_zero 2 hb)
    have hfirstH : cubicOne i 0 A B C = 0 := by
      have hs := cubic_scaling i 0 A B C b hBb
      rw [hAb, hCb, hh] at hs
      exact (mul_eq_zero.mp hs.symm).resolve_left (pow_ne_zero 3 hb)
    by_contra! hz
    have he := CycleQ2GeometricAffineOverlap.cofactor_change_on_curve
      r i 0 A B C b hBb hfirstF hfirstH
    change cofactor (gradQuadricTwo r (A * b) b (C * b))
      (gradCubicTwo i 0 (A * b) b (C * b)) =
      ![-b ^ 2 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 0 +
          A * b ^ 3 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 1,
        b ^ 3 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 1,
        -b ^ 2 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 2 +
          C * b ^ 3 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 1] at he
    rw [hAb, hCb] at he
    have hz1 : cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 1 = 0 := by
      have hs : b ^ 3 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 1 = 0 := by
        simpa [hz 1] using (congrFun he 1).symm
      exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero 3 hb)
    have hz0 : cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 0 = 0 := by
      have hs : -(b ^ 2 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 0) = 0 := by
        simpa [hz 0, hz1] using (congrFun he 0).symm
      exact (mul_eq_zero.mp (neg_eq_zero.mp hs)).resolve_left (pow_ne_zero 2 hb)
    have hz2 : cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 2 = 0 := by
      have hs : -(b ^ 2 * cofactor (gradQuadricOne r A) (gradCubicOne i 0 A B C) 2) = 0 := by
        simpa [hz 2, hz1] using (congrFun he 2).symm
      exact (mul_eq_zero.mp (neg_eq_zero.mp hs)).resolve_left (pow_ne_zero 2 hb)
    obtain ⟨j, hj⟩ := first_chart_jacobian_nonzero i r A B C hi hr hfirstF hfirstH
    fin_cases j
    · exact hj hz0
    · exact hj hz1
    · exact hj hz2

end CycleQ2GeometricSparseCurveSmooth
end
