import HodgeComputer.Constructions.TransitiveCubic.Covariants
import HodgeComputer.Constructions.TransitiveCubic.IdentityEvaluation
import HodgeComputer.Constructions.TransitiveCubic.EncodingCheck
import HodgeComputer.Constructions.PolynomialEncoding.BivariateDifferentiation
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/-! The universal relative differential identity on the affine cubic chart.
The integer covariants use the classical Fisher/SageMath normalization credited
in CubicCovariants. These polynomial identities are proved by Lean arithmetic.
Original cyclic construction by hodgepodgeconjecture; transitive adaptation for fqlx with OpenAI Codex assistance. -/
noncomputable section
namespace TransitiveCovariants
open MvPolynomial
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommRing K]
abbrev Affine (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
local notation "x" => (X (R := K) (0:Fin 2))
local notation "y" => (X (R := K) (1:Fin 2))
def Hpoly (a b c d e f : K) : Affine K :=
  H (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Thetapoly (a b c d e f : K) : Affine K :=
  Theta (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Jpoly (a b c d e f : K) : Affine K :=
  J (C a) (C b) (C c) (C d) (C e) (C f) x y 1
def Upoly (a b c d e f : K) : Affine K :=
  C a*x^3+C b*y^3+C c+C d*x^2*y+C e*y^2+C f*x^2

/-! The relative differential identity is checked one coefficient at a time.
The same proved diagonal-weight and positional encoding as the cubic syzygy
bind every exact integer check to the original parameter polynomial. No native
computation is trusted. This avoids expanding the complete identity with ring.
Original encoding by hodgepodgeconjecture; transitive adaptation for fqlx with
OpenAI Codex assistance. -/
namespace DifferentialData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open TransitiveCovariants.Reflection TransitiveCovariants.IdentityData
open TransitiveCubicEncodingCheck
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
def Hx_2_0 : Expr := (.mul (.natCast 3) H_3_0)
def Hx_1_1 : Expr := (.mul (.natCast 2) H_2_1)
def Hx_1_0 : Expr := (.mul (.natCast 2) H_2_0)
def Hx_0_2 : Expr := (.mul (.natCast 1) H_1_2)
def Hx_0_1 : Expr := (.mul (.natCast 1) H_1_1)
def Hx_0_0 : Expr := (.mul (.natCast 1) H_1_0)
def HxData : Biv := (.cons Hx_2_0 2 0 (.cons Hx_1_1 1 1 (.cons Hx_1_0 1 0 (.cons Hx_0_2 0 2 (.cons Hx_0_1 0 1 (.cons Hx_0_0 0 0 .nil))))))
lemma Hx_generated : dx HData=HxData := by rfl
def Hy_2_0 : Expr := (.mul (.natCast 1) H_2_1)
def Hy_1_1 : Expr := (.mul (.natCast 2) H_1_2)
def Hy_1_0 : Expr := (.mul (.natCast 1) H_1_1)
def Hy_0_2 : Expr := (.mul (.natCast 3) H_0_3)
def Hy_0_1 : Expr := (.mul (.natCast 2) H_0_2)
def Hy_0_0 : Expr := (.mul (.natCast 1) H_0_1)
def HyData : Biv := (.cons Hy_2_0 2 0 (.cons Hy_1_1 1 1 (.cons Hy_1_0 1 0 (.cons Hy_0_2 0 2 (.cons Hy_0_1 0 1 (.cons Hy_0_0 0 0 .nil))))))
lemma Hy_generated : dy HData=HyData := by rfl
def Thetax_5_0 : Expr := (.mul (.natCast 6) Theta_6_0)
def Thetax_4_1 : Expr := (.mul (.natCast 5) Theta_5_1)
def Thetax_4_0 : Expr := (.mul (.natCast 5) Theta_5_0)
def Thetax_3_2 : Expr := (.mul (.natCast 4) Theta_4_2)
def Thetax_3_1 : Expr := (.mul (.natCast 4) Theta_4_1)
def Thetax_3_0 : Expr := (.mul (.natCast 4) Theta_4_0)
def Thetax_2_3 : Expr := (.mul (.natCast 3) Theta_3_3)
def Thetax_2_2 : Expr := (.mul (.natCast 3) Theta_3_2)
def Thetax_2_1 : Expr := (.mul (.natCast 3) Theta_3_1)
def Thetax_2_0 : Expr := (.mul (.natCast 3) Theta_3_0)
def Thetax_1_4 : Expr := (.mul (.natCast 2) Theta_2_4)
def Thetax_1_3 : Expr := (.mul (.natCast 2) Theta_2_3)
def Thetax_1_2 : Expr := (.mul (.natCast 2) Theta_2_2)
def Thetax_1_1 : Expr := (.mul (.natCast 2) Theta_2_1)
def Thetax_1_0 : Expr := (.mul (.natCast 2) Theta_2_0)
def Thetax_0_5 : Expr := (.mul (.natCast 1) Theta_1_5)
def Thetax_0_4 : Expr := (.mul (.natCast 1) Theta_1_4)
def Thetax_0_3 : Expr := (.mul (.natCast 1) Theta_1_3)
def Thetax_0_2 : Expr := (.mul (.natCast 1) Theta_1_2)
def Thetax_0_1 : Expr := (.mul (.natCast 1) Theta_1_1)
def Thetax_0_0 : Expr := (.mul (.natCast 1) Theta_1_0)
def ThetaxData : Biv := (.cons Thetax_5_0 5 0 (.cons Thetax_4_1 4 1 (.cons Thetax_4_0 4 0 (.cons Thetax_3_2 3 2 (.cons Thetax_3_1 3 1 (.cons Thetax_3_0 3 0 (.cons Thetax_2_3 2 3 (.cons Thetax_2_2 2 2 (.cons Thetax_2_1 2 1 (.cons Thetax_2_0 2 0 (.cons Thetax_1_4 1 4 (.cons Thetax_1_3 1 3 (.cons Thetax_1_2 1 2 (.cons Thetax_1_1 1 1 (.cons Thetax_1_0 1 0 (.cons Thetax_0_5 0 5 (.cons Thetax_0_4 0 4 (.cons Thetax_0_3 0 3 (.cons Thetax_0_2 0 2 (.cons Thetax_0_1 0 1 (.cons Thetax_0_0 0 0 .nil)))))))))))))))))))))
lemma Thetax_generated : dx ThetaData=ThetaxData := by rfl
def Thetay_5_0 : Expr := (.mul (.natCast 1) Theta_5_1)
def Thetay_4_1 : Expr := (.mul (.natCast 2) Theta_4_2)
def Thetay_4_0 : Expr := (.mul (.natCast 1) Theta_4_1)
def Thetay_3_2 : Expr := (.mul (.natCast 3) Theta_3_3)
def Thetay_3_1 : Expr := (.mul (.natCast 2) Theta_3_2)
def Thetay_3_0 : Expr := (.mul (.natCast 1) Theta_3_1)
def Thetay_2_3 : Expr := (.mul (.natCast 4) Theta_2_4)
def Thetay_2_2 : Expr := (.mul (.natCast 3) Theta_2_3)
def Thetay_2_1 : Expr := (.mul (.natCast 2) Theta_2_2)
def Thetay_2_0 : Expr := (.mul (.natCast 1) Theta_2_1)
def Thetay_1_4 : Expr := (.mul (.natCast 5) Theta_1_5)
def Thetay_1_3 : Expr := (.mul (.natCast 4) Theta_1_4)
def Thetay_1_2 : Expr := (.mul (.natCast 3) Theta_1_3)
def Thetay_1_1 : Expr := (.mul (.natCast 2) Theta_1_2)
def Thetay_1_0 : Expr := (.mul (.natCast 1) Theta_1_1)
def Thetay_0_5 : Expr := (.mul (.natCast 6) Theta_0_6)
def Thetay_0_4 : Expr := (.mul (.natCast 5) Theta_0_5)
def Thetay_0_3 : Expr := (.mul (.natCast 4) Theta_0_4)
def Thetay_0_2 : Expr := (.mul (.natCast 3) Theta_0_3)
def Thetay_0_1 : Expr := (.mul (.natCast 2) Theta_0_2)
def Thetay_0_0 : Expr := (.mul (.natCast 1) Theta_0_1)
def ThetayData : Biv := (.cons Thetay_5_0 5 0 (.cons Thetay_4_1 4 1 (.cons Thetay_4_0 4 0 (.cons Thetay_3_2 3 2 (.cons Thetay_3_1 3 1 (.cons Thetay_3_0 3 0 (.cons Thetay_2_3 2 3 (.cons Thetay_2_2 2 2 (.cons Thetay_2_1 2 1 (.cons Thetay_2_0 2 0 (.cons Thetay_1_4 1 4 (.cons Thetay_1_3 1 3 (.cons Thetay_1_2 1 2 (.cons Thetay_1_1 1 1 (.cons Thetay_1_0 1 0 (.cons Thetay_0_5 0 5 (.cons Thetay_0_4 0 4 (.cons Thetay_0_3 0 3 (.cons Thetay_0_2 0 2 (.cons Thetay_0_1 0 1 (.cons Thetay_0_0 0 0 .nil)))))))))))))))))))))
lemma Thetay_generated : dy ThetaData=ThetayData := by rfl
def Ux_2_0 : Expr := (.mul (.natCast 3) U_3_0)
def Ux_1_1 : Expr := (.mul (.natCast 2) U_2_1)
def Ux_1_0 : Expr := (.mul (.natCast 2) U_2_0)
def UxData : Biv := (.cons Ux_2_0 2 0 (.cons Ux_1_1 1 1 (.cons Ux_1_0 1 0 .nil)))
lemma Ux_generated : dx UData=UxData := by rfl
def Uy_2_0 : Expr := (.mul (.natCast 1) U_2_1)
def Uy_0_2 : Expr := (.mul (.natCast 3) U_0_3)
def Uy_0_1 : Expr := (.mul (.natCast 2) U_0_2)
def UyData : Biv := (.cons Uy_2_0 2 0 (.cons Uy_0_2 0 2 (.cons Uy_0_1 0 1 .nil)))
lemma Uy_generated : dy UData=UyData := by rfl
def A0_7_0 : Expr := (.mul Ux_2_0 Thetay_5_0)
def A0_6_1 : Expr := (.add (.mul Ux_2_0 Thetay_4_1) (.mul Ux_1_1 Thetay_5_0))
def A0_6_0 : Expr := (.add (.mul Ux_2_0 Thetay_4_0) (.mul Ux_1_0 Thetay_5_0))
def A0_5_2 : Expr := (.add (.mul Ux_2_0 Thetay_3_2) (.mul Ux_1_1 Thetay_4_1))
def A0_5_1 : Expr := (.add (.mul Ux_2_0 Thetay_3_1) (.add (.mul Ux_1_1 Thetay_4_0) (.mul Ux_1_0 Thetay_4_1)))
def A0_5_0 : Expr := (.add (.mul Ux_2_0 Thetay_3_0) (.mul Ux_1_0 Thetay_4_0))
def A0_4_3 : Expr := (.add (.mul Ux_2_0 Thetay_2_3) (.mul Ux_1_1 Thetay_3_2))
def A0_4_2 : Expr := (.add (.mul Ux_2_0 Thetay_2_2) (.add (.mul Ux_1_1 Thetay_3_1) (.mul Ux_1_0 Thetay_3_2)))
def A0_4_1 : Expr := (.add (.mul Ux_2_0 Thetay_2_1) (.add (.mul Ux_1_1 Thetay_3_0) (.mul Ux_1_0 Thetay_3_1)))
def A0_4_0 : Expr := (.add (.mul Ux_2_0 Thetay_2_0) (.mul Ux_1_0 Thetay_3_0))
def A0_3_4 : Expr := (.add (.mul Ux_2_0 Thetay_1_4) (.mul Ux_1_1 Thetay_2_3))
def A0_3_3 : Expr := (.add (.mul Ux_2_0 Thetay_1_3) (.add (.mul Ux_1_1 Thetay_2_2) (.mul Ux_1_0 Thetay_2_3)))
def A0_3_2 : Expr := (.add (.mul Ux_2_0 Thetay_1_2) (.add (.mul Ux_1_1 Thetay_2_1) (.mul Ux_1_0 Thetay_2_2)))
def A0_3_1 : Expr := (.add (.mul Ux_2_0 Thetay_1_1) (.add (.mul Ux_1_1 Thetay_2_0) (.mul Ux_1_0 Thetay_2_1)))
def A0_3_0 : Expr := (.add (.mul Ux_2_0 Thetay_1_0) (.mul Ux_1_0 Thetay_2_0))
def A0_2_5 : Expr := (.add (.mul Ux_2_0 Thetay_0_5) (.mul Ux_1_1 Thetay_1_4))
def A0_2_4 : Expr := (.add (.mul Ux_2_0 Thetay_0_4) (.add (.mul Ux_1_1 Thetay_1_3) (.mul Ux_1_0 Thetay_1_4)))
def A0_2_3 : Expr := (.add (.mul Ux_2_0 Thetay_0_3) (.add (.mul Ux_1_1 Thetay_1_2) (.mul Ux_1_0 Thetay_1_3)))
def A0_2_2 : Expr := (.add (.mul Ux_2_0 Thetay_0_2) (.add (.mul Ux_1_1 Thetay_1_1) (.mul Ux_1_0 Thetay_1_2)))
def A0_2_1 : Expr := (.add (.mul Ux_2_0 Thetay_0_1) (.add (.mul Ux_1_1 Thetay_1_0) (.mul Ux_1_0 Thetay_1_1)))
def A0_2_0 : Expr := (.add (.mul Ux_2_0 Thetay_0_0) (.mul Ux_1_0 Thetay_1_0))
def A0_1_6 : Expr := (.mul Ux_1_1 Thetay_0_5)
def A0_1_5 : Expr := (.add (.mul Ux_1_1 Thetay_0_4) (.mul Ux_1_0 Thetay_0_5))
def A0_1_4 : Expr := (.add (.mul Ux_1_1 Thetay_0_3) (.mul Ux_1_0 Thetay_0_4))
def A0_1_3 : Expr := (.add (.mul Ux_1_1 Thetay_0_2) (.mul Ux_1_0 Thetay_0_3))
def A0_1_2 : Expr := (.add (.mul Ux_1_1 Thetay_0_1) (.mul Ux_1_0 Thetay_0_2))
def A0_1_1 : Expr := (.add (.mul Ux_1_1 Thetay_0_0) (.mul Ux_1_0 Thetay_0_1))
def A0_1_0 : Expr := (.mul Ux_1_0 Thetay_0_0)
def A0Data : Biv := (.cons A0_7_0 7 0 (.cons A0_6_1 6 1 (.cons A0_6_0 6 0 (.cons A0_5_2 5 2 (.cons A0_5_1 5 1 (.cons A0_5_0 5 0 (.cons A0_4_3 4 3 (.cons A0_4_2 4 2 (.cons A0_4_1 4 1 (.cons A0_4_0 4 0 (.cons A0_3_4 3 4 (.cons A0_3_3 3 3 (.cons A0_3_2 3 2 (.cons A0_3_1 3 1 (.cons A0_3_0 3 0 (.cons A0_2_5 2 5 (.cons A0_2_4 2 4 (.cons A0_2_3 2 3 (.cons A0_2_2 2 2 (.cons A0_2_1 2 1 (.cons A0_2_0 2 0 (.cons A0_1_6 1 6 (.cons A0_1_5 1 5 (.cons A0_1_4 1 4 (.cons A0_1_3 1 3 (.cons A0_1_2 1 2 (.cons A0_1_1 1 1 (.cons A0_1_0 1 0 .nil))))))))))))))))))))))))))))
lemma A0_generated : multiply UxData ThetayData=A0Data := by rfl
def A1_7_0 : Expr := (.mul Uy_2_0 Thetax_5_0)
def A1_6_1 : Expr := (.mul Uy_2_0 Thetax_4_1)
def A1_6_0 : Expr := (.mul Uy_2_0 Thetax_4_0)
def A1_5_2 : Expr := (.add (.mul Uy_2_0 Thetax_3_2) (.mul Uy_0_2 Thetax_5_0))
def A1_5_1 : Expr := (.add (.mul Uy_2_0 Thetax_3_1) (.mul Uy_0_1 Thetax_5_0))
def A1_5_0 : Expr := (.mul Uy_2_0 Thetax_3_0)
def A1_4_3 : Expr := (.add (.mul Uy_2_0 Thetax_2_3) (.mul Uy_0_2 Thetax_4_1))
def A1_4_2 : Expr := (.add (.mul Uy_2_0 Thetax_2_2) (.add (.mul Uy_0_2 Thetax_4_0) (.mul Uy_0_1 Thetax_4_1)))
def A1_4_1 : Expr := (.add (.mul Uy_2_0 Thetax_2_1) (.mul Uy_0_1 Thetax_4_0))
def A1_4_0 : Expr := (.mul Uy_2_0 Thetax_2_0)
def A1_3_4 : Expr := (.add (.mul Uy_2_0 Thetax_1_4) (.mul Uy_0_2 Thetax_3_2))
def A1_3_3 : Expr := (.add (.mul Uy_2_0 Thetax_1_3) (.add (.mul Uy_0_2 Thetax_3_1) (.mul Uy_0_1 Thetax_3_2)))
def A1_3_2 : Expr := (.add (.mul Uy_2_0 Thetax_1_2) (.add (.mul Uy_0_2 Thetax_3_0) (.mul Uy_0_1 Thetax_3_1)))
def A1_3_1 : Expr := (.add (.mul Uy_2_0 Thetax_1_1) (.mul Uy_0_1 Thetax_3_0))
def A1_3_0 : Expr := (.mul Uy_2_0 Thetax_1_0)
def A1_2_5 : Expr := (.add (.mul Uy_2_0 Thetax_0_5) (.mul Uy_0_2 Thetax_2_3))
def A1_2_4 : Expr := (.add (.mul Uy_2_0 Thetax_0_4) (.add (.mul Uy_0_2 Thetax_2_2) (.mul Uy_0_1 Thetax_2_3)))
def A1_2_3 : Expr := (.add (.mul Uy_2_0 Thetax_0_3) (.add (.mul Uy_0_2 Thetax_2_1) (.mul Uy_0_1 Thetax_2_2)))
def A1_2_2 : Expr := (.add (.mul Uy_2_0 Thetax_0_2) (.add (.mul Uy_0_2 Thetax_2_0) (.mul Uy_0_1 Thetax_2_1)))
def A1_2_1 : Expr := (.add (.mul Uy_2_0 Thetax_0_1) (.mul Uy_0_1 Thetax_2_0))
def A1_2_0 : Expr := (.mul Uy_2_0 Thetax_0_0)
def A1_1_6 : Expr := (.mul Uy_0_2 Thetax_1_4)
def A1_1_5 : Expr := (.add (.mul Uy_0_2 Thetax_1_3) (.mul Uy_0_1 Thetax_1_4))
def A1_1_4 : Expr := (.add (.mul Uy_0_2 Thetax_1_2) (.mul Uy_0_1 Thetax_1_3))
def A1_1_3 : Expr := (.add (.mul Uy_0_2 Thetax_1_1) (.mul Uy_0_1 Thetax_1_2))
def A1_1_2 : Expr := (.add (.mul Uy_0_2 Thetax_1_0) (.mul Uy_0_1 Thetax_1_1))
def A1_1_1 : Expr := (.mul Uy_0_1 Thetax_1_0)
def A1_0_7 : Expr := (.mul Uy_0_2 Thetax_0_5)
def A1_0_6 : Expr := (.add (.mul Uy_0_2 Thetax_0_4) (.mul Uy_0_1 Thetax_0_5))
def A1_0_5 : Expr := (.add (.mul Uy_0_2 Thetax_0_3) (.mul Uy_0_1 Thetax_0_4))
def A1_0_4 : Expr := (.add (.mul Uy_0_2 Thetax_0_2) (.mul Uy_0_1 Thetax_0_3))
def A1_0_3 : Expr := (.add (.mul Uy_0_2 Thetax_0_1) (.mul Uy_0_1 Thetax_0_2))
def A1_0_2 : Expr := (.add (.mul Uy_0_2 Thetax_0_0) (.mul Uy_0_1 Thetax_0_1))
def A1_0_1 : Expr := (.mul Uy_0_1 Thetax_0_0)
def A1Data : Biv := (.cons A1_7_0 7 0 (.cons A1_6_1 6 1 (.cons A1_6_0 6 0 (.cons A1_5_2 5 2 (.cons A1_5_1 5 1 (.cons A1_5_0 5 0 (.cons A1_4_3 4 3 (.cons A1_4_2 4 2 (.cons A1_4_1 4 1 (.cons A1_4_0 4 0 (.cons A1_3_4 3 4 (.cons A1_3_3 3 3 (.cons A1_3_2 3 2 (.cons A1_3_1 3 1 (.cons A1_3_0 3 0 (.cons A1_2_5 2 5 (.cons A1_2_4 2 4 (.cons A1_2_3 2 3 (.cons A1_2_2 2 2 (.cons A1_2_1 2 1 (.cons A1_2_0 2 0 (.cons A1_1_6 1 6 (.cons A1_1_5 1 5 (.cons A1_1_4 1 4 (.cons A1_1_3 1 3 (.cons A1_1_2 1 2 (.cons A1_1_1 1 1 (.cons A1_0_7 0 7 (.cons A1_0_6 0 6 (.cons A1_0_5 0 5 (.cons A1_0_4 0 4 (.cons A1_0_3 0 3 (.cons A1_0_2 0 2 (.cons A1_0_1 0 1 .nil))))))))))))))))))))))))))))))))))
lemma A1_generated : multiply UyData ThetaxData=A1Data := by rfl
def A1n_7_0 : Expr := (.mul (.neg (.num 1)) A1_7_0)
def A1n_6_1 : Expr := (.mul (.neg (.num 1)) A1_6_1)
def A1n_6_0 : Expr := (.mul (.neg (.num 1)) A1_6_0)
def A1n_5_2 : Expr := (.mul (.neg (.num 1)) A1_5_2)
def A1n_5_1 : Expr := (.mul (.neg (.num 1)) A1_5_1)
def A1n_5_0 : Expr := (.mul (.neg (.num 1)) A1_5_0)
def A1n_4_3 : Expr := (.mul (.neg (.num 1)) A1_4_3)
def A1n_4_2 : Expr := (.mul (.neg (.num 1)) A1_4_2)
def A1n_4_1 : Expr := (.mul (.neg (.num 1)) A1_4_1)
def A1n_4_0 : Expr := (.mul (.neg (.num 1)) A1_4_0)
def A1n_3_4 : Expr := (.mul (.neg (.num 1)) A1_3_4)
def A1n_3_3 : Expr := (.mul (.neg (.num 1)) A1_3_3)
def A1n_3_2 : Expr := (.mul (.neg (.num 1)) A1_3_2)
def A1n_3_1 : Expr := (.mul (.neg (.num 1)) A1_3_1)
def A1n_3_0 : Expr := (.mul (.neg (.num 1)) A1_3_0)
def A1n_2_5 : Expr := (.mul (.neg (.num 1)) A1_2_5)
def A1n_2_4 : Expr := (.mul (.neg (.num 1)) A1_2_4)
def A1n_2_3 : Expr := (.mul (.neg (.num 1)) A1_2_3)
def A1n_2_2 : Expr := (.mul (.neg (.num 1)) A1_2_2)
def A1n_2_1 : Expr := (.mul (.neg (.num 1)) A1_2_1)
def A1n_2_0 : Expr := (.mul (.neg (.num 1)) A1_2_0)
def A1n_1_6 : Expr := (.mul (.neg (.num 1)) A1_1_6)
def A1n_1_5 : Expr := (.mul (.neg (.num 1)) A1_1_5)
def A1n_1_4 : Expr := (.mul (.neg (.num 1)) A1_1_4)
def A1n_1_3 : Expr := (.mul (.neg (.num 1)) A1_1_3)
def A1n_1_2 : Expr := (.mul (.neg (.num 1)) A1_1_2)
def A1n_1_1 : Expr := (.mul (.neg (.num 1)) A1_1_1)
def A1n_0_7 : Expr := (.mul (.neg (.num 1)) A1_0_7)
def A1n_0_6 : Expr := (.mul (.neg (.num 1)) A1_0_6)
def A1n_0_5 : Expr := (.mul (.neg (.num 1)) A1_0_5)
def A1n_0_4 : Expr := (.mul (.neg (.num 1)) A1_0_4)
def A1n_0_3 : Expr := (.mul (.neg (.num 1)) A1_0_3)
def A1n_0_2 : Expr := (.mul (.neg (.num 1)) A1_0_2)
def A1n_0_1 : Expr := (.mul (.neg (.num 1)) A1_0_1)
def A1nData : Biv := (.cons A1n_7_0 7 0 (.cons A1n_6_1 6 1 (.cons A1n_6_0 6 0 (.cons A1n_5_2 5 2 (.cons A1n_5_1 5 1 (.cons A1n_5_0 5 0 (.cons A1n_4_3 4 3 (.cons A1n_4_2 4 2 (.cons A1n_4_1 4 1 (.cons A1n_4_0 4 0 (.cons A1n_3_4 3 4 (.cons A1n_3_3 3 3 (.cons A1n_3_2 3 2 (.cons A1n_3_1 3 1 (.cons A1n_3_0 3 0 (.cons A1n_2_5 2 5 (.cons A1n_2_4 2 4 (.cons A1n_2_3 2 3 (.cons A1n_2_2 2 2 (.cons A1n_2_1 2 1 (.cons A1n_2_0 2 0 (.cons A1n_1_6 1 6 (.cons A1n_1_5 1 5 (.cons A1n_1_4 1 4 (.cons A1n_1_3 1 3 (.cons A1n_1_2 1 2 (.cons A1n_1_1 1 1 (.cons A1n_0_7 0 7 (.cons A1n_0_6 0 6 (.cons A1n_0_5 0 5 (.cons A1n_0_4 0 4 (.cons A1n_0_3 0 3 (.cons A1n_0_2 0 2 (.cons A1n_0_1 0 1 .nil))))))))))))))))))))))))))))))))))
lemma A1n_generated : scale (.neg (.num 1)) 0 0 A1Data=A1nData := by rfl
def A_7_0 : Expr := (.add A0_7_0 A1n_7_0)
def A_6_1 : Expr := (.add A0_6_1 A1n_6_1)
def A_6_0 : Expr := (.add A0_6_0 A1n_6_0)
def A_5_2 : Expr := (.add A0_5_2 A1n_5_2)
def A_5_1 : Expr := (.add A0_5_1 A1n_5_1)
def A_5_0 : Expr := (.add A0_5_0 A1n_5_0)
def A_4_3 : Expr := (.add A0_4_3 A1n_4_3)
def A_4_2 : Expr := (.add A0_4_2 A1n_4_2)
def A_4_1 : Expr := (.add A0_4_1 A1n_4_1)
def A_4_0 : Expr := (.add A0_4_0 A1n_4_0)
def A_3_4 : Expr := (.add A0_3_4 A1n_3_4)
def A_3_3 : Expr := (.add A0_3_3 A1n_3_3)
def A_3_2 : Expr := (.add A0_3_2 A1n_3_2)
def A_3_1 : Expr := (.add A0_3_1 A1n_3_1)
def A_3_0 : Expr := (.add A0_3_0 A1n_3_0)
def A_2_5 : Expr := (.add A0_2_5 A1n_2_5)
def A_2_4 : Expr := (.add A0_2_4 A1n_2_4)
def A_2_3 : Expr := (.add A0_2_3 A1n_2_3)
def A_2_2 : Expr := (.add A0_2_2 A1n_2_2)
def A_2_1 : Expr := (.add A0_2_1 A1n_2_1)
def A_2_0 : Expr := (.add A0_2_0 A1n_2_0)
def A_1_6 : Expr := (.add A0_1_6 A1n_1_6)
def A_1_5 : Expr := (.add A0_1_5 A1n_1_5)
def A_1_4 : Expr := (.add A0_1_4 A1n_1_4)
def A_1_3 : Expr := (.add A0_1_3 A1n_1_3)
def A_1_2 : Expr := (.add A0_1_2 A1n_1_2)
def A_1_1 : Expr := (.add A0_1_1 A1n_1_1)
def A_1_0 : Expr := A0_1_0
def A_0_7 : Expr := A1n_0_7
def A_0_6 : Expr := A1n_0_6
def A_0_5 : Expr := A1n_0_5
def A_0_4 : Expr := A1n_0_4
def A_0_3 : Expr := A1n_0_3
def A_0_2 : Expr := A1n_0_2
def A_0_1 : Expr := A1n_0_1
def AData : Biv := (.cons A_7_0 7 0 (.cons A_6_1 6 1 (.cons A_6_0 6 0 (.cons A_5_2 5 2 (.cons A_5_1 5 1 (.cons A_5_0 5 0 (.cons A_4_3 4 3 (.cons A_4_2 4 2 (.cons A_4_1 4 1 (.cons A_4_0 4 0 (.cons A_3_4 3 4 (.cons A_3_3 3 3 (.cons A_3_2 3 2 (.cons A_3_1 3 1 (.cons A_3_0 3 0 (.cons A_2_5 2 5 (.cons A_2_4 2 4 (.cons A_2_3 2 3 (.cons A_2_2 2 2 (.cons A_2_1 2 1 (.cons A_2_0 2 0 (.cons A_1_6 1 6 (.cons A_1_5 1 5 (.cons A_1_4 1 4 (.cons A_1_3 1 3 (.cons A_1_2 1 2 (.cons A_1_1 1 1 (.cons A_1_0 1 0 (.cons A_0_7 0 7 (.cons A_0_6 0 6 (.cons A_0_5 0 5 (.cons A_0_4 0 4 (.cons A_0_3 0 3 (.cons A_0_2 0 2 (.cons A_0_1 0 1 .nil)))))))))))))))))))))))))))))))))))
lemma A_generated : merge 512 A0Data A1nData=AData := by rfl
def HA_10_0 : Expr := (.mul H_3_0 A_7_0)
def HA_9_1 : Expr := (.add (.mul H_3_0 A_6_1) (.mul H_2_1 A_7_0))
def HA_9_0 : Expr := (.add (.mul H_3_0 A_6_0) (.mul H_2_0 A_7_0))
def HA_8_2 : Expr := (.add (.mul H_3_0 A_5_2) (.add (.mul H_2_1 A_6_1) (.mul H_1_2 A_7_0)))
def HA_8_1 : Expr := (.add (.mul H_3_0 A_5_1) (.add (.mul H_2_1 A_6_0) (.add (.mul H_2_0 A_6_1) (.mul H_1_1 A_7_0))))
def HA_8_0 : Expr := (.add (.mul H_3_0 A_5_0) (.add (.mul H_2_0 A_6_0) (.mul H_1_0 A_7_0)))
def HA_7_3 : Expr := (.add (.mul H_3_0 A_4_3) (.add (.mul H_2_1 A_5_2) (.add (.mul H_1_2 A_6_1) (.mul H_0_3 A_7_0))))
def HA_7_2 : Expr := (.add (.mul H_3_0 A_4_2) (.add (.mul H_2_1 A_5_1) (.add (.mul H_2_0 A_5_2) (.add (.mul H_1_2 A_6_0) (.add (.mul H_1_1 A_6_1) (.mul H_0_2 A_7_0))))))
def HA_7_1 : Expr := (.add (.mul H_3_0 A_4_1) (.add (.mul H_2_1 A_5_0) (.add (.mul H_2_0 A_5_1) (.add (.mul H_1_1 A_6_0) (.add (.mul H_1_0 A_6_1) (.mul H_0_1 A_7_0))))))
def HA_7_0 : Expr := (.add (.mul H_3_0 A_4_0) (.add (.mul H_2_0 A_5_0) (.add (.mul H_1_0 A_6_0) (.mul H_0_0 A_7_0))))
def HA_6_4 : Expr := (.add (.mul H_3_0 A_3_4) (.add (.mul H_2_1 A_4_3) (.add (.mul H_1_2 A_5_2) (.mul H_0_3 A_6_1))))
def HA_6_3 : Expr := (.add (.mul H_3_0 A_3_3) (.add (.mul H_2_1 A_4_2) (.add (.mul H_2_0 A_4_3) (.add (.mul H_1_2 A_5_1) (.add (.mul H_1_1 A_5_2) (.add (.mul H_0_3 A_6_0) (.mul H_0_2 A_6_1)))))))
def HA_6_2 : Expr := (.add (.mul H_3_0 A_3_2) (.add (.mul H_2_1 A_4_1) (.add (.mul H_2_0 A_4_2) (.add (.mul H_1_2 A_5_0) (.add (.mul H_1_1 A_5_1) (.add (.mul H_1_0 A_5_2) (.add (.mul H_0_2 A_6_0) (.mul H_0_1 A_6_1))))))))
def HA_6_1 : Expr := (.add (.mul H_3_0 A_3_1) (.add (.mul H_2_1 A_4_0) (.add (.mul H_2_0 A_4_1) (.add (.mul H_1_1 A_5_0) (.add (.mul H_1_0 A_5_1) (.add (.mul H_0_1 A_6_0) (.mul H_0_0 A_6_1)))))))
def HA_6_0 : Expr := (.add (.mul H_3_0 A_3_0) (.add (.mul H_2_0 A_4_0) (.add (.mul H_1_0 A_5_0) (.mul H_0_0 A_6_0))))
def HA_5_5 : Expr := (.add (.mul H_3_0 A_2_5) (.add (.mul H_2_1 A_3_4) (.add (.mul H_1_2 A_4_3) (.mul H_0_3 A_5_2))))
def HA_5_4 : Expr := (.add (.mul H_3_0 A_2_4) (.add (.mul H_2_1 A_3_3) (.add (.mul H_2_0 A_3_4) (.add (.mul H_1_2 A_4_2) (.add (.mul H_1_1 A_4_3) (.add (.mul H_0_3 A_5_1) (.mul H_0_2 A_5_2)))))))
def HA_5_3 : Expr := (.add (.mul H_3_0 A_2_3) (.add (.mul H_2_1 A_3_2) (.add (.mul H_2_0 A_3_3) (.add (.mul H_1_2 A_4_1) (.add (.mul H_1_1 A_4_2) (.add (.mul H_1_0 A_4_3) (.add (.mul H_0_3 A_5_0) (.add (.mul H_0_2 A_5_1) (.mul H_0_1 A_5_2)))))))))
def HA_5_2 : Expr := (.add (.mul H_3_0 A_2_2) (.add (.mul H_2_1 A_3_1) (.add (.mul H_2_0 A_3_2) (.add (.mul H_1_2 A_4_0) (.add (.mul H_1_1 A_4_1) (.add (.mul H_1_0 A_4_2) (.add (.mul H_0_2 A_5_0) (.add (.mul H_0_1 A_5_1) (.mul H_0_0 A_5_2)))))))))
def HA_5_1 : Expr := (.add (.mul H_3_0 A_2_1) (.add (.mul H_2_1 A_3_0) (.add (.mul H_2_0 A_3_1) (.add (.mul H_1_1 A_4_0) (.add (.mul H_1_0 A_4_1) (.add (.mul H_0_1 A_5_0) (.mul H_0_0 A_5_1)))))))
def HA_5_0 : Expr := (.add (.mul H_3_0 A_2_0) (.add (.mul H_2_0 A_3_0) (.add (.mul H_1_0 A_4_0) (.mul H_0_0 A_5_0))))
def HA_4_6 : Expr := (.add (.mul H_3_0 A_1_6) (.add (.mul H_2_1 A_2_5) (.add (.mul H_1_2 A_3_4) (.mul H_0_3 A_4_3))))
def HA_4_5 : Expr := (.add (.mul H_3_0 A_1_5) (.add (.mul H_2_1 A_2_4) (.add (.mul H_2_0 A_2_5) (.add (.mul H_1_2 A_3_3) (.add (.mul H_1_1 A_3_4) (.add (.mul H_0_3 A_4_2) (.mul H_0_2 A_4_3)))))))
def HA_4_4 : Expr := (.add (.mul H_3_0 A_1_4) (.add (.mul H_2_1 A_2_3) (.add (.mul H_2_0 A_2_4) (.add (.mul H_1_2 A_3_2) (.add (.mul H_1_1 A_3_3) (.add (.mul H_1_0 A_3_4) (.add (.mul H_0_3 A_4_1) (.add (.mul H_0_2 A_4_2) (.mul H_0_1 A_4_3)))))))))
def HA_4_3 : Expr := (.add (.mul H_3_0 A_1_3) (.add (.mul H_2_1 A_2_2) (.add (.mul H_2_0 A_2_3) (.add (.mul H_1_2 A_3_1) (.add (.mul H_1_1 A_3_2) (.add (.mul H_1_0 A_3_3) (.add (.mul H_0_3 A_4_0) (.add (.mul H_0_2 A_4_1) (.add (.mul H_0_1 A_4_2) (.mul H_0_0 A_4_3))))))))))
def HA_4_2 : Expr := (.add (.mul H_3_0 A_1_2) (.add (.mul H_2_1 A_2_1) (.add (.mul H_2_0 A_2_2) (.add (.mul H_1_2 A_3_0) (.add (.mul H_1_1 A_3_1) (.add (.mul H_1_0 A_3_2) (.add (.mul H_0_2 A_4_0) (.add (.mul H_0_1 A_4_1) (.mul H_0_0 A_4_2)))))))))
def HA_4_1 : Expr := (.add (.mul H_3_0 A_1_1) (.add (.mul H_2_1 A_2_0) (.add (.mul H_2_0 A_2_1) (.add (.mul H_1_1 A_3_0) (.add (.mul H_1_0 A_3_1) (.add (.mul H_0_1 A_4_0) (.mul H_0_0 A_4_1)))))))
def HA_4_0 : Expr := (.add (.mul H_3_0 A_1_0) (.add (.mul H_2_0 A_2_0) (.add (.mul H_1_0 A_3_0) (.mul H_0_0 A_4_0))))
def HA_3_7 : Expr := (.add (.mul H_3_0 A_0_7) (.add (.mul H_2_1 A_1_6) (.add (.mul H_1_2 A_2_5) (.mul H_0_3 A_3_4))))
def HA_3_6 : Expr := (.add (.mul H_3_0 A_0_6) (.add (.mul H_2_1 A_1_5) (.add (.mul H_2_0 A_1_6) (.add (.mul H_1_2 A_2_4) (.add (.mul H_1_1 A_2_5) (.add (.mul H_0_3 A_3_3) (.mul H_0_2 A_3_4)))))))
def HA_3_5 : Expr := (.add (.mul H_3_0 A_0_5) (.add (.mul H_2_1 A_1_4) (.add (.mul H_2_0 A_1_5) (.add (.mul H_1_2 A_2_3) (.add (.mul H_1_1 A_2_4) (.add (.mul H_1_0 A_2_5) (.add (.mul H_0_3 A_3_2) (.add (.mul H_0_2 A_3_3) (.mul H_0_1 A_3_4)))))))))
def HA_3_4 : Expr := (.add (.mul H_3_0 A_0_4) (.add (.mul H_2_1 A_1_3) (.add (.mul H_2_0 A_1_4) (.add (.mul H_1_2 A_2_2) (.add (.mul H_1_1 A_2_3) (.add (.mul H_1_0 A_2_4) (.add (.mul H_0_3 A_3_1) (.add (.mul H_0_2 A_3_2) (.add (.mul H_0_1 A_3_3) (.mul H_0_0 A_3_4))))))))))
def HA_3_3 : Expr := (.add (.mul H_3_0 A_0_3) (.add (.mul H_2_1 A_1_2) (.add (.mul H_2_0 A_1_3) (.add (.mul H_1_2 A_2_1) (.add (.mul H_1_1 A_2_2) (.add (.mul H_1_0 A_2_3) (.add (.mul H_0_3 A_3_0) (.add (.mul H_0_2 A_3_1) (.add (.mul H_0_1 A_3_2) (.mul H_0_0 A_3_3))))))))))
def HA_3_2 : Expr := (.add (.mul H_3_0 A_0_2) (.add (.mul H_2_1 A_1_1) (.add (.mul H_2_0 A_1_2) (.add (.mul H_1_2 A_2_0) (.add (.mul H_1_1 A_2_1) (.add (.mul H_1_0 A_2_2) (.add (.mul H_0_2 A_3_0) (.add (.mul H_0_1 A_3_1) (.mul H_0_0 A_3_2)))))))))
def HA_3_1 : Expr := (.add (.mul H_3_0 A_0_1) (.add (.mul H_2_1 A_1_0) (.add (.mul H_2_0 A_1_1) (.add (.mul H_1_1 A_2_0) (.add (.mul H_1_0 A_2_1) (.add (.mul H_0_1 A_3_0) (.mul H_0_0 A_3_1)))))))
def HA_3_0 : Expr := (.add (.mul H_2_0 A_1_0) (.add (.mul H_1_0 A_2_0) (.mul H_0_0 A_3_0)))
def HA_2_8 : Expr := (.add (.mul H_2_1 A_0_7) (.add (.mul H_1_2 A_1_6) (.mul H_0_3 A_2_5)))
def HA_2_7 : Expr := (.add (.mul H_2_1 A_0_6) (.add (.mul H_2_0 A_0_7) (.add (.mul H_1_2 A_1_5) (.add (.mul H_1_1 A_1_6) (.add (.mul H_0_3 A_2_4) (.mul H_0_2 A_2_5))))))
def HA_2_6 : Expr := (.add (.mul H_2_1 A_0_5) (.add (.mul H_2_0 A_0_6) (.add (.mul H_1_2 A_1_4) (.add (.mul H_1_1 A_1_5) (.add (.mul H_1_0 A_1_6) (.add (.mul H_0_3 A_2_3) (.add (.mul H_0_2 A_2_4) (.mul H_0_1 A_2_5))))))))
def HA_2_5 : Expr := (.add (.mul H_2_1 A_0_4) (.add (.mul H_2_0 A_0_5) (.add (.mul H_1_2 A_1_3) (.add (.mul H_1_1 A_1_4) (.add (.mul H_1_0 A_1_5) (.add (.mul H_0_3 A_2_2) (.add (.mul H_0_2 A_2_3) (.add (.mul H_0_1 A_2_4) (.mul H_0_0 A_2_5)))))))))
def HA_2_4 : Expr := (.add (.mul H_2_1 A_0_3) (.add (.mul H_2_0 A_0_4) (.add (.mul H_1_2 A_1_2) (.add (.mul H_1_1 A_1_3) (.add (.mul H_1_0 A_1_4) (.add (.mul H_0_3 A_2_1) (.add (.mul H_0_2 A_2_2) (.add (.mul H_0_1 A_2_3) (.mul H_0_0 A_2_4)))))))))
def HA_2_3 : Expr := (.add (.mul H_2_1 A_0_2) (.add (.mul H_2_0 A_0_3) (.add (.mul H_1_2 A_1_1) (.add (.mul H_1_1 A_1_2) (.add (.mul H_1_0 A_1_3) (.add (.mul H_0_3 A_2_0) (.add (.mul H_0_2 A_2_1) (.add (.mul H_0_1 A_2_2) (.mul H_0_0 A_2_3)))))))))
def HA_2_2 : Expr := (.add (.mul H_2_1 A_0_1) (.add (.mul H_2_0 A_0_2) (.add (.mul H_1_2 A_1_0) (.add (.mul H_1_1 A_1_1) (.add (.mul H_1_0 A_1_2) (.add (.mul H_0_2 A_2_0) (.add (.mul H_0_1 A_2_1) (.mul H_0_0 A_2_2))))))))
def HA_2_1 : Expr := (.add (.mul H_2_0 A_0_1) (.add (.mul H_1_1 A_1_0) (.add (.mul H_1_0 A_1_1) (.add (.mul H_0_1 A_2_0) (.mul H_0_0 A_2_1)))))
def HA_2_0 : Expr := (.add (.mul H_1_0 A_1_0) (.mul H_0_0 A_2_0))
def HA_1_9 : Expr := (.add (.mul H_1_2 A_0_7) (.mul H_0_3 A_1_6))
def HA_1_8 : Expr := (.add (.mul H_1_2 A_0_6) (.add (.mul H_1_1 A_0_7) (.add (.mul H_0_3 A_1_5) (.mul H_0_2 A_1_6))))
def HA_1_7 : Expr := (.add (.mul H_1_2 A_0_5) (.add (.mul H_1_1 A_0_6) (.add (.mul H_1_0 A_0_7) (.add (.mul H_0_3 A_1_4) (.add (.mul H_0_2 A_1_5) (.mul H_0_1 A_1_6))))))
def HA_1_6 : Expr := (.add (.mul H_1_2 A_0_4) (.add (.mul H_1_1 A_0_5) (.add (.mul H_1_0 A_0_6) (.add (.mul H_0_3 A_1_3) (.add (.mul H_0_2 A_1_4) (.add (.mul H_0_1 A_1_5) (.mul H_0_0 A_1_6)))))))
def HA_1_5 : Expr := (.add (.mul H_1_2 A_0_3) (.add (.mul H_1_1 A_0_4) (.add (.mul H_1_0 A_0_5) (.add (.mul H_0_3 A_1_2) (.add (.mul H_0_2 A_1_3) (.add (.mul H_0_1 A_1_4) (.mul H_0_0 A_1_5)))))))
def HA_1_4 : Expr := (.add (.mul H_1_2 A_0_2) (.add (.mul H_1_1 A_0_3) (.add (.mul H_1_0 A_0_4) (.add (.mul H_0_3 A_1_1) (.add (.mul H_0_2 A_1_2) (.add (.mul H_0_1 A_1_3) (.mul H_0_0 A_1_4)))))))
def HA_1_3 : Expr := (.add (.mul H_1_2 A_0_1) (.add (.mul H_1_1 A_0_2) (.add (.mul H_1_0 A_0_3) (.add (.mul H_0_3 A_1_0) (.add (.mul H_0_2 A_1_1) (.add (.mul H_0_1 A_1_2) (.mul H_0_0 A_1_3)))))))
def HA_1_2 : Expr := (.add (.mul H_1_1 A_0_1) (.add (.mul H_1_0 A_0_2) (.add (.mul H_0_2 A_1_0) (.add (.mul H_0_1 A_1_1) (.mul H_0_0 A_1_2)))))
def HA_1_1 : Expr := (.add (.mul H_1_0 A_0_1) (.add (.mul H_0_1 A_1_0) (.mul H_0_0 A_1_1)))
def HA_1_0 : Expr := (.mul H_0_0 A_1_0)
def HA_0_10 : Expr := (.mul H_0_3 A_0_7)
def HA_0_9 : Expr := (.add (.mul H_0_3 A_0_6) (.mul H_0_2 A_0_7))
def HA_0_8 : Expr := (.add (.mul H_0_3 A_0_5) (.add (.mul H_0_2 A_0_6) (.mul H_0_1 A_0_7)))
def HA_0_7 : Expr := (.add (.mul H_0_3 A_0_4) (.add (.mul H_0_2 A_0_5) (.add (.mul H_0_1 A_0_6) (.mul H_0_0 A_0_7))))
def HA_0_6 : Expr := (.add (.mul H_0_3 A_0_3) (.add (.mul H_0_2 A_0_4) (.add (.mul H_0_1 A_0_5) (.mul H_0_0 A_0_6))))
def HA_0_5 : Expr := (.add (.mul H_0_3 A_0_2) (.add (.mul H_0_2 A_0_3) (.add (.mul H_0_1 A_0_4) (.mul H_0_0 A_0_5))))
def HA_0_4 : Expr := (.add (.mul H_0_3 A_0_1) (.add (.mul H_0_2 A_0_2) (.add (.mul H_0_1 A_0_3) (.mul H_0_0 A_0_4))))
def HA_0_3 : Expr := (.add (.mul H_0_2 A_0_1) (.add (.mul H_0_1 A_0_2) (.mul H_0_0 A_0_3)))
def HA_0_2 : Expr := (.add (.mul H_0_1 A_0_1) (.mul H_0_0 A_0_2))
def HA_0_1 : Expr := (.mul H_0_0 A_0_1)
def HAData : Biv := (.cons HA_10_0 10 0 (.cons HA_9_1 9 1 (.cons HA_9_0 9 0 (.cons HA_8_2 8 2 (.cons HA_8_1 8 1 (.cons HA_8_0 8 0 (.cons HA_7_3 7 3 (.cons HA_7_2 7 2 (.cons HA_7_1 7 1 (.cons HA_7_0 7 0 (.cons HA_6_4 6 4 (.cons HA_6_3 6 3 (.cons HA_6_2 6 2 (.cons HA_6_1 6 1 (.cons HA_6_0 6 0 (.cons HA_5_5 5 5 (.cons HA_5_4 5 4 (.cons HA_5_3 5 3 (.cons HA_5_2 5 2 (.cons HA_5_1 5 1 (.cons HA_5_0 5 0 (.cons HA_4_6 4 6 (.cons HA_4_5 4 5 (.cons HA_4_4 4 4 (.cons HA_4_3 4 3 (.cons HA_4_2 4 2 (.cons HA_4_1 4 1 (.cons HA_4_0 4 0 (.cons HA_3_7 3 7 (.cons HA_3_6 3 6 (.cons HA_3_5 3 5 (.cons HA_3_4 3 4 (.cons HA_3_3 3 3 (.cons HA_3_2 3 2 (.cons HA_3_1 3 1 (.cons HA_3_0 3 0 (.cons HA_2_8 2 8 (.cons HA_2_7 2 7 (.cons HA_2_6 2 6 (.cons HA_2_5 2 5 (.cons HA_2_4 2 4 (.cons HA_2_3 2 3 (.cons HA_2_2 2 2 (.cons HA_2_1 2 1 (.cons HA_2_0 2 0 (.cons HA_1_9 1 9 (.cons HA_1_8 1 8 (.cons HA_1_7 1 7 (.cons HA_1_6 1 6 (.cons HA_1_5 1 5 (.cons HA_1_4 1 4 (.cons HA_1_3 1 3 (.cons HA_1_2 1 2 (.cons HA_1_1 1 1 (.cons HA_1_0 1 0 (.cons HA_0_10 0 10 (.cons HA_0_9 0 9 (.cons HA_0_8 0 8 (.cons HA_0_7 0 7 (.cons HA_0_6 0 6 (.cons HA_0_5 0 5 (.cons HA_0_4 0 4 (.cons HA_0_3 0 3 (.cons HA_0_2 0 2 (.cons HA_0_1 0 1 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma HA_generated : multiply HData AData=HAData := by rfl
def B0_4_0 : Expr := (.mul Ux_2_0 Hy_2_0)
def B0_3_1 : Expr := (.add (.mul Ux_2_0 Hy_1_1) (.mul Ux_1_1 Hy_2_0))
def B0_3_0 : Expr := (.add (.mul Ux_2_0 Hy_1_0) (.mul Ux_1_0 Hy_2_0))
def B0_2_2 : Expr := (.add (.mul Ux_2_0 Hy_0_2) (.mul Ux_1_1 Hy_1_1))
def B0_2_1 : Expr := (.add (.mul Ux_2_0 Hy_0_1) (.add (.mul Ux_1_1 Hy_1_0) (.mul Ux_1_0 Hy_1_1)))
def B0_2_0 : Expr := (.add (.mul Ux_2_0 Hy_0_0) (.mul Ux_1_0 Hy_1_0))
def B0_1_3 : Expr := (.mul Ux_1_1 Hy_0_2)
def B0_1_2 : Expr := (.add (.mul Ux_1_1 Hy_0_1) (.mul Ux_1_0 Hy_0_2))
def B0_1_1 : Expr := (.add (.mul Ux_1_1 Hy_0_0) (.mul Ux_1_0 Hy_0_1))
def B0_1_0 : Expr := (.mul Ux_1_0 Hy_0_0)
def B0Data : Biv := (.cons B0_4_0 4 0 (.cons B0_3_1 3 1 (.cons B0_3_0 3 0 (.cons B0_2_2 2 2 (.cons B0_2_1 2 1 (.cons B0_2_0 2 0 (.cons B0_1_3 1 3 (.cons B0_1_2 1 2 (.cons B0_1_1 1 1 (.cons B0_1_0 1 0 .nil))))))))))
lemma B0_generated : multiply UxData HyData=B0Data := by rfl
def B1_4_0 : Expr := (.mul Uy_2_0 Hx_2_0)
def B1_3_1 : Expr := (.mul Uy_2_0 Hx_1_1)
def B1_3_0 : Expr := (.mul Uy_2_0 Hx_1_0)
def B1_2_2 : Expr := (.add (.mul Uy_2_0 Hx_0_2) (.mul Uy_0_2 Hx_2_0))
def B1_2_1 : Expr := (.add (.mul Uy_2_0 Hx_0_1) (.mul Uy_0_1 Hx_2_0))
def B1_2_0 : Expr := (.mul Uy_2_0 Hx_0_0)
def B1_1_3 : Expr := (.mul Uy_0_2 Hx_1_1)
def B1_1_2 : Expr := (.add (.mul Uy_0_2 Hx_1_0) (.mul Uy_0_1 Hx_1_1))
def B1_1_1 : Expr := (.mul Uy_0_1 Hx_1_0)
def B1_0_4 : Expr := (.mul Uy_0_2 Hx_0_2)
def B1_0_3 : Expr := (.add (.mul Uy_0_2 Hx_0_1) (.mul Uy_0_1 Hx_0_2))
def B1_0_2 : Expr := (.add (.mul Uy_0_2 Hx_0_0) (.mul Uy_0_1 Hx_0_1))
def B1_0_1 : Expr := (.mul Uy_0_1 Hx_0_0)
def B1Data : Biv := (.cons B1_4_0 4 0 (.cons B1_3_1 3 1 (.cons B1_3_0 3 0 (.cons B1_2_2 2 2 (.cons B1_2_1 2 1 (.cons B1_2_0 2 0 (.cons B1_1_3 1 3 (.cons B1_1_2 1 2 (.cons B1_1_1 1 1 (.cons B1_0_4 0 4 (.cons B1_0_3 0 3 (.cons B1_0_2 0 2 (.cons B1_0_1 0 1 .nil)))))))))))))
lemma B1_generated : multiply UyData HxData=B1Data := by rfl
def B1n_4_0 : Expr := (.mul (.neg (.num 1)) B1_4_0)
def B1n_3_1 : Expr := (.mul (.neg (.num 1)) B1_3_1)
def B1n_3_0 : Expr := (.mul (.neg (.num 1)) B1_3_0)
def B1n_2_2 : Expr := (.mul (.neg (.num 1)) B1_2_2)
def B1n_2_1 : Expr := (.mul (.neg (.num 1)) B1_2_1)
def B1n_2_0 : Expr := (.mul (.neg (.num 1)) B1_2_0)
def B1n_1_3 : Expr := (.mul (.neg (.num 1)) B1_1_3)
def B1n_1_2 : Expr := (.mul (.neg (.num 1)) B1_1_2)
def B1n_1_1 : Expr := (.mul (.neg (.num 1)) B1_1_1)
def B1n_0_4 : Expr := (.mul (.neg (.num 1)) B1_0_4)
def B1n_0_3 : Expr := (.mul (.neg (.num 1)) B1_0_3)
def B1n_0_2 : Expr := (.mul (.neg (.num 1)) B1_0_2)
def B1n_0_1 : Expr := (.mul (.neg (.num 1)) B1_0_1)
def B1nData : Biv := (.cons B1n_4_0 4 0 (.cons B1n_3_1 3 1 (.cons B1n_3_0 3 0 (.cons B1n_2_2 2 2 (.cons B1n_2_1 2 1 (.cons B1n_2_0 2 0 (.cons B1n_1_3 1 3 (.cons B1n_1_2 1 2 (.cons B1n_1_1 1 1 (.cons B1n_0_4 0 4 (.cons B1n_0_3 0 3 (.cons B1n_0_2 0 2 (.cons B1n_0_1 0 1 .nil)))))))))))))
lemma B1n_generated : scale (.neg (.num 1)) 0 0 B1Data=B1nData := by rfl
def B_4_0 : Expr := (.add B0_4_0 B1n_4_0)
def B_3_1 : Expr := (.add B0_3_1 B1n_3_1)
def B_3_0 : Expr := (.add B0_3_0 B1n_3_0)
def B_2_2 : Expr := (.add B0_2_2 B1n_2_2)
def B_2_1 : Expr := (.add B0_2_1 B1n_2_1)
def B_2_0 : Expr := (.add B0_2_0 B1n_2_0)
def B_1_3 : Expr := (.add B0_1_3 B1n_1_3)
def B_1_2 : Expr := (.add B0_1_2 B1n_1_2)
def B_1_1 : Expr := (.add B0_1_1 B1n_1_1)
def B_1_0 : Expr := B0_1_0
def B_0_4 : Expr := B1n_0_4
def B_0_3 : Expr := B1n_0_3
def B_0_2 : Expr := B1n_0_2
def B_0_1 : Expr := B1n_0_1
def BData : Biv := (.cons B_4_0 4 0 (.cons B_3_1 3 1 (.cons B_3_0 3 0 (.cons B_2_2 2 2 (.cons B_2_1 2 1 (.cons B_2_0 2 0 (.cons B_1_3 1 3 (.cons B_1_2 1 2 (.cons B_1_1 1 1 (.cons B_1_0 1 0 (.cons B_0_4 0 4 (.cons B_0_3 0 3 (.cons B_0_2 0 2 (.cons B_0_1 0 1 .nil))))))))))))))
lemma B_generated : merge 512 B0Data B1nData=BData := by rfl
def QB_10_0 : Expr := (.mul Theta_6_0 B_4_0)
def QB_9_1 : Expr := (.add (.mul Theta_6_0 B_3_1) (.mul Theta_5_1 B_4_0))
def QB_9_0 : Expr := (.add (.mul Theta_6_0 B_3_0) (.mul Theta_5_0 B_4_0))
def QB_8_2 : Expr := (.add (.mul Theta_6_0 B_2_2) (.add (.mul Theta_5_1 B_3_1) (.mul Theta_4_2 B_4_0)))
def QB_8_1 : Expr := (.add (.mul Theta_6_0 B_2_1) (.add (.mul Theta_5_1 B_3_0) (.add (.mul Theta_5_0 B_3_1) (.mul Theta_4_1 B_4_0))))
def QB_8_0 : Expr := (.add (.mul Theta_6_0 B_2_0) (.add (.mul Theta_5_0 B_3_0) (.mul Theta_4_0 B_4_0)))
def QB_7_3 : Expr := (.add (.mul Theta_6_0 B_1_3) (.add (.mul Theta_5_1 B_2_2) (.add (.mul Theta_4_2 B_3_1) (.mul Theta_3_3 B_4_0))))
def QB_7_2 : Expr := (.add (.mul Theta_6_0 B_1_2) (.add (.mul Theta_5_1 B_2_1) (.add (.mul Theta_5_0 B_2_2) (.add (.mul Theta_4_2 B_3_0) (.add (.mul Theta_4_1 B_3_1) (.mul Theta_3_2 B_4_0))))))
def QB_7_1 : Expr := (.add (.mul Theta_6_0 B_1_1) (.add (.mul Theta_5_1 B_2_0) (.add (.mul Theta_5_0 B_2_1) (.add (.mul Theta_4_1 B_3_0) (.add (.mul Theta_4_0 B_3_1) (.mul Theta_3_1 B_4_0))))))
def QB_7_0 : Expr := (.add (.mul Theta_6_0 B_1_0) (.add (.mul Theta_5_0 B_2_0) (.add (.mul Theta_4_0 B_3_0) (.mul Theta_3_0 B_4_0))))
def QB_6_4 : Expr := (.add (.mul Theta_6_0 B_0_4) (.add (.mul Theta_5_1 B_1_3) (.add (.mul Theta_4_2 B_2_2) (.add (.mul Theta_3_3 B_3_1) (.mul Theta_2_4 B_4_0)))))
def QB_6_3 : Expr := (.add (.mul Theta_6_0 B_0_3) (.add (.mul Theta_5_1 B_1_2) (.add (.mul Theta_5_0 B_1_3) (.add (.mul Theta_4_2 B_2_1) (.add (.mul Theta_4_1 B_2_2) (.add (.mul Theta_3_3 B_3_0) (.add (.mul Theta_3_2 B_3_1) (.mul Theta_2_3 B_4_0))))))))
def QB_6_2 : Expr := (.add (.mul Theta_6_0 B_0_2) (.add (.mul Theta_5_1 B_1_1) (.add (.mul Theta_5_0 B_1_2) (.add (.mul Theta_4_2 B_2_0) (.add (.mul Theta_4_1 B_2_1) (.add (.mul Theta_4_0 B_2_2) (.add (.mul Theta_3_2 B_3_0) (.add (.mul Theta_3_1 B_3_1) (.mul Theta_2_2 B_4_0)))))))))
def QB_6_1 : Expr := (.add (.mul Theta_6_0 B_0_1) (.add (.mul Theta_5_1 B_1_0) (.add (.mul Theta_5_0 B_1_1) (.add (.mul Theta_4_1 B_2_0) (.add (.mul Theta_4_0 B_2_1) (.add (.mul Theta_3_1 B_3_0) (.add (.mul Theta_3_0 B_3_1) (.mul Theta_2_1 B_4_0))))))))
def QB_6_0 : Expr := (.add (.mul Theta_5_0 B_1_0) (.add (.mul Theta_4_0 B_2_0) (.add (.mul Theta_3_0 B_3_0) (.mul Theta_2_0 B_4_0))))
def QB_5_5 : Expr := (.add (.mul Theta_5_1 B_0_4) (.add (.mul Theta_4_2 B_1_3) (.add (.mul Theta_3_3 B_2_2) (.add (.mul Theta_2_4 B_3_1) (.mul Theta_1_5 B_4_0)))))
def QB_5_4 : Expr := (.add (.mul Theta_5_1 B_0_3) (.add (.mul Theta_5_0 B_0_4) (.add (.mul Theta_4_2 B_1_2) (.add (.mul Theta_4_1 B_1_3) (.add (.mul Theta_3_3 B_2_1) (.add (.mul Theta_3_2 B_2_2) (.add (.mul Theta_2_4 B_3_0) (.add (.mul Theta_2_3 B_3_1) (.mul Theta_1_4 B_4_0)))))))))
def QB_5_3 : Expr := (.add (.mul Theta_5_1 B_0_2) (.add (.mul Theta_5_0 B_0_3) (.add (.mul Theta_4_2 B_1_1) (.add (.mul Theta_4_1 B_1_2) (.add (.mul Theta_4_0 B_1_3) (.add (.mul Theta_3_3 B_2_0) (.add (.mul Theta_3_2 B_2_1) (.add (.mul Theta_3_1 B_2_2) (.add (.mul Theta_2_3 B_3_0) (.add (.mul Theta_2_2 B_3_1) (.mul Theta_1_3 B_4_0)))))))))))
def QB_5_2 : Expr := (.add (.mul Theta_5_1 B_0_1) (.add (.mul Theta_5_0 B_0_2) (.add (.mul Theta_4_2 B_1_0) (.add (.mul Theta_4_1 B_1_1) (.add (.mul Theta_4_0 B_1_2) (.add (.mul Theta_3_2 B_2_0) (.add (.mul Theta_3_1 B_2_1) (.add (.mul Theta_3_0 B_2_2) (.add (.mul Theta_2_2 B_3_0) (.add (.mul Theta_2_1 B_3_1) (.mul Theta_1_2 B_4_0)))))))))))
def QB_5_1 : Expr := (.add (.mul Theta_5_0 B_0_1) (.add (.mul Theta_4_1 B_1_0) (.add (.mul Theta_4_0 B_1_1) (.add (.mul Theta_3_1 B_2_0) (.add (.mul Theta_3_0 B_2_1) (.add (.mul Theta_2_1 B_3_0) (.add (.mul Theta_2_0 B_3_1) (.mul Theta_1_1 B_4_0))))))))
def QB_5_0 : Expr := (.add (.mul Theta_4_0 B_1_0) (.add (.mul Theta_3_0 B_2_0) (.add (.mul Theta_2_0 B_3_0) (.mul Theta_1_0 B_4_0))))
def QB_4_6 : Expr := (.add (.mul Theta_4_2 B_0_4) (.add (.mul Theta_3_3 B_1_3) (.add (.mul Theta_2_4 B_2_2) (.add (.mul Theta_1_5 B_3_1) (.mul Theta_0_6 B_4_0)))))
def QB_4_5 : Expr := (.add (.mul Theta_4_2 B_0_3) (.add (.mul Theta_4_1 B_0_4) (.add (.mul Theta_3_3 B_1_2) (.add (.mul Theta_3_2 B_1_3) (.add (.mul Theta_2_4 B_2_1) (.add (.mul Theta_2_3 B_2_2) (.add (.mul Theta_1_5 B_3_0) (.add (.mul Theta_1_4 B_3_1) (.mul Theta_0_5 B_4_0)))))))))
def QB_4_4 : Expr := (.add (.mul Theta_4_2 B_0_2) (.add (.mul Theta_4_1 B_0_3) (.add (.mul Theta_4_0 B_0_4) (.add (.mul Theta_3_3 B_1_1) (.add (.mul Theta_3_2 B_1_2) (.add (.mul Theta_3_1 B_1_3) (.add (.mul Theta_2_4 B_2_0) (.add (.mul Theta_2_3 B_2_1) (.add (.mul Theta_2_2 B_2_2) (.add (.mul Theta_1_4 B_3_0) (.add (.mul Theta_1_3 B_3_1) (.mul Theta_0_4 B_4_0))))))))))))
def QB_4_3 : Expr := (.add (.mul Theta_4_2 B_0_1) (.add (.mul Theta_4_1 B_0_2) (.add (.mul Theta_4_0 B_0_3) (.add (.mul Theta_3_3 B_1_0) (.add (.mul Theta_3_2 B_1_1) (.add (.mul Theta_3_1 B_1_2) (.add (.mul Theta_3_0 B_1_3) (.add (.mul Theta_2_3 B_2_0) (.add (.mul Theta_2_2 B_2_1) (.add (.mul Theta_2_1 B_2_2) (.add (.mul Theta_1_3 B_3_0) (.add (.mul Theta_1_2 B_3_1) (.mul Theta_0_3 B_4_0)))))))))))))
def QB_4_2 : Expr := (.add (.mul Theta_4_1 B_0_1) (.add (.mul Theta_4_0 B_0_2) (.add (.mul Theta_3_2 B_1_0) (.add (.mul Theta_3_1 B_1_1) (.add (.mul Theta_3_0 B_1_2) (.add (.mul Theta_2_2 B_2_0) (.add (.mul Theta_2_1 B_2_1) (.add (.mul Theta_2_0 B_2_2) (.add (.mul Theta_1_2 B_3_0) (.add (.mul Theta_1_1 B_3_1) (.mul Theta_0_2 B_4_0)))))))))))
def QB_4_1 : Expr := (.add (.mul Theta_4_0 B_0_1) (.add (.mul Theta_3_1 B_1_0) (.add (.mul Theta_3_0 B_1_1) (.add (.mul Theta_2_1 B_2_0) (.add (.mul Theta_2_0 B_2_1) (.add (.mul Theta_1_1 B_3_0) (.add (.mul Theta_1_0 B_3_1) (.mul Theta_0_1 B_4_0))))))))
def QB_4_0 : Expr := (.add (.mul Theta_3_0 B_1_0) (.add (.mul Theta_2_0 B_2_0) (.add (.mul Theta_1_0 B_3_0) (.mul Theta_0_0 B_4_0))))
def QB_3_7 : Expr := (.add (.mul Theta_3_3 B_0_4) (.add (.mul Theta_2_4 B_1_3) (.add (.mul Theta_1_5 B_2_2) (.mul Theta_0_6 B_3_1))))
def QB_3_6 : Expr := (.add (.mul Theta_3_3 B_0_3) (.add (.mul Theta_3_2 B_0_4) (.add (.mul Theta_2_4 B_1_2) (.add (.mul Theta_2_3 B_1_3) (.add (.mul Theta_1_5 B_2_1) (.add (.mul Theta_1_4 B_2_2) (.add (.mul Theta_0_6 B_3_0) (.mul Theta_0_5 B_3_1))))))))
def QB_3_5 : Expr := (.add (.mul Theta_3_3 B_0_2) (.add (.mul Theta_3_2 B_0_3) (.add (.mul Theta_3_1 B_0_4) (.add (.mul Theta_2_4 B_1_1) (.add (.mul Theta_2_3 B_1_2) (.add (.mul Theta_2_2 B_1_3) (.add (.mul Theta_1_5 B_2_0) (.add (.mul Theta_1_4 B_2_1) (.add (.mul Theta_1_3 B_2_2) (.add (.mul Theta_0_5 B_3_0) (.mul Theta_0_4 B_3_1)))))))))))
def QB_3_4 : Expr := (.add (.mul Theta_3_3 B_0_1) (.add (.mul Theta_3_2 B_0_2) (.add (.mul Theta_3_1 B_0_3) (.add (.mul Theta_3_0 B_0_4) (.add (.mul Theta_2_4 B_1_0) (.add (.mul Theta_2_3 B_1_1) (.add (.mul Theta_2_2 B_1_2) (.add (.mul Theta_2_1 B_1_3) (.add (.mul Theta_1_4 B_2_0) (.add (.mul Theta_1_3 B_2_1) (.add (.mul Theta_1_2 B_2_2) (.add (.mul Theta_0_4 B_3_0) (.mul Theta_0_3 B_3_1)))))))))))))
def QB_3_3 : Expr := (.add (.mul Theta_3_2 B_0_1) (.add (.mul Theta_3_1 B_0_2) (.add (.mul Theta_3_0 B_0_3) (.add (.mul Theta_2_3 B_1_0) (.add (.mul Theta_2_2 B_1_1) (.add (.mul Theta_2_1 B_1_2) (.add (.mul Theta_2_0 B_1_3) (.add (.mul Theta_1_3 B_2_0) (.add (.mul Theta_1_2 B_2_1) (.add (.mul Theta_1_1 B_2_2) (.add (.mul Theta_0_3 B_3_0) (.mul Theta_0_2 B_3_1))))))))))))
def QB_3_2 : Expr := (.add (.mul Theta_3_1 B_0_1) (.add (.mul Theta_3_0 B_0_2) (.add (.mul Theta_2_2 B_1_0) (.add (.mul Theta_2_1 B_1_1) (.add (.mul Theta_2_0 B_1_2) (.add (.mul Theta_1_2 B_2_0) (.add (.mul Theta_1_1 B_2_1) (.add (.mul Theta_1_0 B_2_2) (.add (.mul Theta_0_2 B_3_0) (.mul Theta_0_1 B_3_1))))))))))
def QB_3_1 : Expr := (.add (.mul Theta_3_0 B_0_1) (.add (.mul Theta_2_1 B_1_0) (.add (.mul Theta_2_0 B_1_1) (.add (.mul Theta_1_1 B_2_0) (.add (.mul Theta_1_0 B_2_1) (.add (.mul Theta_0_1 B_3_0) (.mul Theta_0_0 B_3_1)))))))
def QB_3_0 : Expr := (.add (.mul Theta_2_0 B_1_0) (.add (.mul Theta_1_0 B_2_0) (.mul Theta_0_0 B_3_0)))
def QB_2_8 : Expr := (.add (.mul Theta_2_4 B_0_4) (.add (.mul Theta_1_5 B_1_3) (.mul Theta_0_6 B_2_2)))
def QB_2_7 : Expr := (.add (.mul Theta_2_4 B_0_3) (.add (.mul Theta_2_3 B_0_4) (.add (.mul Theta_1_5 B_1_2) (.add (.mul Theta_1_4 B_1_3) (.add (.mul Theta_0_6 B_2_1) (.mul Theta_0_5 B_2_2))))))
def QB_2_6 : Expr := (.add (.mul Theta_2_4 B_0_2) (.add (.mul Theta_2_3 B_0_3) (.add (.mul Theta_2_2 B_0_4) (.add (.mul Theta_1_5 B_1_1) (.add (.mul Theta_1_4 B_1_2) (.add (.mul Theta_1_3 B_1_3) (.add (.mul Theta_0_6 B_2_0) (.add (.mul Theta_0_5 B_2_1) (.mul Theta_0_4 B_2_2)))))))))
def QB_2_5 : Expr := (.add (.mul Theta_2_4 B_0_1) (.add (.mul Theta_2_3 B_0_2) (.add (.mul Theta_2_2 B_0_3) (.add (.mul Theta_2_1 B_0_4) (.add (.mul Theta_1_5 B_1_0) (.add (.mul Theta_1_4 B_1_1) (.add (.mul Theta_1_3 B_1_2) (.add (.mul Theta_1_2 B_1_3) (.add (.mul Theta_0_5 B_2_0) (.add (.mul Theta_0_4 B_2_1) (.mul Theta_0_3 B_2_2)))))))))))
def QB_2_4 : Expr := (.add (.mul Theta_2_3 B_0_1) (.add (.mul Theta_2_2 B_0_2) (.add (.mul Theta_2_1 B_0_3) (.add (.mul Theta_2_0 B_0_4) (.add (.mul Theta_1_4 B_1_0) (.add (.mul Theta_1_3 B_1_1) (.add (.mul Theta_1_2 B_1_2) (.add (.mul Theta_1_1 B_1_3) (.add (.mul Theta_0_4 B_2_0) (.add (.mul Theta_0_3 B_2_1) (.mul Theta_0_2 B_2_2)))))))))))
def QB_2_3 : Expr := (.add (.mul Theta_2_2 B_0_1) (.add (.mul Theta_2_1 B_0_2) (.add (.mul Theta_2_0 B_0_3) (.add (.mul Theta_1_3 B_1_0) (.add (.mul Theta_1_2 B_1_1) (.add (.mul Theta_1_1 B_1_2) (.add (.mul Theta_1_0 B_1_3) (.add (.mul Theta_0_3 B_2_0) (.add (.mul Theta_0_2 B_2_1) (.mul Theta_0_1 B_2_2))))))))))
def QB_2_2 : Expr := (.add (.mul Theta_2_1 B_0_1) (.add (.mul Theta_2_0 B_0_2) (.add (.mul Theta_1_2 B_1_0) (.add (.mul Theta_1_1 B_1_1) (.add (.mul Theta_1_0 B_1_2) (.add (.mul Theta_0_2 B_2_0) (.add (.mul Theta_0_1 B_2_1) (.mul Theta_0_0 B_2_2))))))))
def QB_2_1 : Expr := (.add (.mul Theta_2_0 B_0_1) (.add (.mul Theta_1_1 B_1_0) (.add (.mul Theta_1_0 B_1_1) (.add (.mul Theta_0_1 B_2_0) (.mul Theta_0_0 B_2_1)))))
def QB_2_0 : Expr := (.add (.mul Theta_1_0 B_1_0) (.mul Theta_0_0 B_2_0))
def QB_1_9 : Expr := (.add (.mul Theta_1_5 B_0_4) (.mul Theta_0_6 B_1_3))
def QB_1_8 : Expr := (.add (.mul Theta_1_5 B_0_3) (.add (.mul Theta_1_4 B_0_4) (.add (.mul Theta_0_6 B_1_2) (.mul Theta_0_5 B_1_3))))
def QB_1_7 : Expr := (.add (.mul Theta_1_5 B_0_2) (.add (.mul Theta_1_4 B_0_3) (.add (.mul Theta_1_3 B_0_4) (.add (.mul Theta_0_6 B_1_1) (.add (.mul Theta_0_5 B_1_2) (.mul Theta_0_4 B_1_3))))))
def QB_1_6 : Expr := (.add (.mul Theta_1_5 B_0_1) (.add (.mul Theta_1_4 B_0_2) (.add (.mul Theta_1_3 B_0_3) (.add (.mul Theta_1_2 B_0_4) (.add (.mul Theta_0_6 B_1_0) (.add (.mul Theta_0_5 B_1_1) (.add (.mul Theta_0_4 B_1_2) (.mul Theta_0_3 B_1_3))))))))
def QB_1_5 : Expr := (.add (.mul Theta_1_4 B_0_1) (.add (.mul Theta_1_3 B_0_2) (.add (.mul Theta_1_2 B_0_3) (.add (.mul Theta_1_1 B_0_4) (.add (.mul Theta_0_5 B_1_0) (.add (.mul Theta_0_4 B_1_1) (.add (.mul Theta_0_3 B_1_2) (.mul Theta_0_2 B_1_3))))))))
def QB_1_4 : Expr := (.add (.mul Theta_1_3 B_0_1) (.add (.mul Theta_1_2 B_0_2) (.add (.mul Theta_1_1 B_0_3) (.add (.mul Theta_1_0 B_0_4) (.add (.mul Theta_0_4 B_1_0) (.add (.mul Theta_0_3 B_1_1) (.add (.mul Theta_0_2 B_1_2) (.mul Theta_0_1 B_1_3))))))))
def QB_1_3 : Expr := (.add (.mul Theta_1_2 B_0_1) (.add (.mul Theta_1_1 B_0_2) (.add (.mul Theta_1_0 B_0_3) (.add (.mul Theta_0_3 B_1_0) (.add (.mul Theta_0_2 B_1_1) (.add (.mul Theta_0_1 B_1_2) (.mul Theta_0_0 B_1_3)))))))
def QB_1_2 : Expr := (.add (.mul Theta_1_1 B_0_1) (.add (.mul Theta_1_0 B_0_2) (.add (.mul Theta_0_2 B_1_0) (.add (.mul Theta_0_1 B_1_1) (.mul Theta_0_0 B_1_2)))))
def QB_1_1 : Expr := (.add (.mul Theta_1_0 B_0_1) (.add (.mul Theta_0_1 B_1_0) (.mul Theta_0_0 B_1_1)))
def QB_1_0 : Expr := (.mul Theta_0_0 B_1_0)
def QB_0_10 : Expr := (.mul Theta_0_6 B_0_4)
def QB_0_9 : Expr := (.add (.mul Theta_0_6 B_0_3) (.mul Theta_0_5 B_0_4))
def QB_0_8 : Expr := (.add (.mul Theta_0_6 B_0_2) (.add (.mul Theta_0_5 B_0_3) (.mul Theta_0_4 B_0_4)))
def QB_0_7 : Expr := (.add (.mul Theta_0_6 B_0_1) (.add (.mul Theta_0_5 B_0_2) (.add (.mul Theta_0_4 B_0_3) (.mul Theta_0_3 B_0_4))))
def QB_0_6 : Expr := (.add (.mul Theta_0_5 B_0_1) (.add (.mul Theta_0_4 B_0_2) (.add (.mul Theta_0_3 B_0_3) (.mul Theta_0_2 B_0_4))))
def QB_0_5 : Expr := (.add (.mul Theta_0_4 B_0_1) (.add (.mul Theta_0_3 B_0_2) (.add (.mul Theta_0_2 B_0_3) (.mul Theta_0_1 B_0_4))))
def QB_0_4 : Expr := (.add (.mul Theta_0_3 B_0_1) (.add (.mul Theta_0_2 B_0_2) (.add (.mul Theta_0_1 B_0_3) (.mul Theta_0_0 B_0_4))))
def QB_0_3 : Expr := (.add (.mul Theta_0_2 B_0_1) (.add (.mul Theta_0_1 B_0_2) (.mul Theta_0_0 B_0_3)))
def QB_0_2 : Expr := (.add (.mul Theta_0_1 B_0_1) (.mul Theta_0_0 B_0_2))
def QB_0_1 : Expr := (.mul Theta_0_0 B_0_1)
def QBData : Biv := (.cons QB_10_0 10 0 (.cons QB_9_1 9 1 (.cons QB_9_0 9 0 (.cons QB_8_2 8 2 (.cons QB_8_1 8 1 (.cons QB_8_0 8 0 (.cons QB_7_3 7 3 (.cons QB_7_2 7 2 (.cons QB_7_1 7 1 (.cons QB_7_0 7 0 (.cons QB_6_4 6 4 (.cons QB_6_3 6 3 (.cons QB_6_2 6 2 (.cons QB_6_1 6 1 (.cons QB_6_0 6 0 (.cons QB_5_5 5 5 (.cons QB_5_4 5 4 (.cons QB_5_3 5 3 (.cons QB_5_2 5 2 (.cons QB_5_1 5 1 (.cons QB_5_0 5 0 (.cons QB_4_6 4 6 (.cons QB_4_5 4 5 (.cons QB_4_4 4 4 (.cons QB_4_3 4 3 (.cons QB_4_2 4 2 (.cons QB_4_1 4 1 (.cons QB_4_0 4 0 (.cons QB_3_7 3 7 (.cons QB_3_6 3 6 (.cons QB_3_5 3 5 (.cons QB_3_4 3 4 (.cons QB_3_3 3 3 (.cons QB_3_2 3 2 (.cons QB_3_1 3 1 (.cons QB_3_0 3 0 (.cons QB_2_8 2 8 (.cons QB_2_7 2 7 (.cons QB_2_6 2 6 (.cons QB_2_5 2 5 (.cons QB_2_4 2 4 (.cons QB_2_3 2 3 (.cons QB_2_2 2 2 (.cons QB_2_1 2 1 (.cons QB_2_0 2 0 (.cons QB_1_9 1 9 (.cons QB_1_8 1 8 (.cons QB_1_7 1 7 (.cons QB_1_6 1 6 (.cons QB_1_5 1 5 (.cons QB_1_4 1 4 (.cons QB_1_3 1 3 (.cons QB_1_2 1 2 (.cons QB_1_1 1 1 (.cons QB_1_0 1 0 (.cons QB_0_10 0 10 (.cons QB_0_9 0 9 (.cons QB_0_8 0 8 (.cons QB_0_7 0 7 (.cons QB_0_6 0 6 (.cons QB_0_5 0 5 (.cons QB_0_4 0 4 (.cons QB_0_3 0 3 (.cons QB_0_2 0 2 (.cons QB_0_1 0 1 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma QB_generated : multiply ThetaData BData=QBData := by rfl
def QBneg_10_0 : Expr := (.mul (.neg (.num 2)) QB_10_0)
def QBneg_9_1 : Expr := (.mul (.neg (.num 2)) QB_9_1)
def QBneg_9_0 : Expr := (.mul (.neg (.num 2)) QB_9_0)
def QBneg_8_2 : Expr := (.mul (.neg (.num 2)) QB_8_2)
def QBneg_8_1 : Expr := (.mul (.neg (.num 2)) QB_8_1)
def QBneg_8_0 : Expr := (.mul (.neg (.num 2)) QB_8_0)
def QBneg_7_3 : Expr := (.mul (.neg (.num 2)) QB_7_3)
def QBneg_7_2 : Expr := (.mul (.neg (.num 2)) QB_7_2)
def QBneg_7_1 : Expr := (.mul (.neg (.num 2)) QB_7_1)
def QBneg_7_0 : Expr := (.mul (.neg (.num 2)) QB_7_0)
def QBneg_6_4 : Expr := (.mul (.neg (.num 2)) QB_6_4)
def QBneg_6_3 : Expr := (.mul (.neg (.num 2)) QB_6_3)
def QBneg_6_2 : Expr := (.mul (.neg (.num 2)) QB_6_2)
def QBneg_6_1 : Expr := (.mul (.neg (.num 2)) QB_6_1)
def QBneg_6_0 : Expr := (.mul (.neg (.num 2)) QB_6_0)
def QBneg_5_5 : Expr := (.mul (.neg (.num 2)) QB_5_5)
def QBneg_5_4 : Expr := (.mul (.neg (.num 2)) QB_5_4)
def QBneg_5_3 : Expr := (.mul (.neg (.num 2)) QB_5_3)
def QBneg_5_2 : Expr := (.mul (.neg (.num 2)) QB_5_2)
def QBneg_5_1 : Expr := (.mul (.neg (.num 2)) QB_5_1)
def QBneg_5_0 : Expr := (.mul (.neg (.num 2)) QB_5_0)
def QBneg_4_6 : Expr := (.mul (.neg (.num 2)) QB_4_6)
def QBneg_4_5 : Expr := (.mul (.neg (.num 2)) QB_4_5)
def QBneg_4_4 : Expr := (.mul (.neg (.num 2)) QB_4_4)
def QBneg_4_3 : Expr := (.mul (.neg (.num 2)) QB_4_3)
def QBneg_4_2 : Expr := (.mul (.neg (.num 2)) QB_4_2)
def QBneg_4_1 : Expr := (.mul (.neg (.num 2)) QB_4_1)
def QBneg_4_0 : Expr := (.mul (.neg (.num 2)) QB_4_0)
def QBneg_3_7 : Expr := (.mul (.neg (.num 2)) QB_3_7)
def QBneg_3_6 : Expr := (.mul (.neg (.num 2)) QB_3_6)
def QBneg_3_5 : Expr := (.mul (.neg (.num 2)) QB_3_5)
def QBneg_3_4 : Expr := (.mul (.neg (.num 2)) QB_3_4)
def QBneg_3_3 : Expr := (.mul (.neg (.num 2)) QB_3_3)
def QBneg_3_2 : Expr := (.mul (.neg (.num 2)) QB_3_2)
def QBneg_3_1 : Expr := (.mul (.neg (.num 2)) QB_3_1)
def QBneg_3_0 : Expr := (.mul (.neg (.num 2)) QB_3_0)
def QBneg_2_8 : Expr := (.mul (.neg (.num 2)) QB_2_8)
def QBneg_2_7 : Expr := (.mul (.neg (.num 2)) QB_2_7)
def QBneg_2_6 : Expr := (.mul (.neg (.num 2)) QB_2_6)
def QBneg_2_5 : Expr := (.mul (.neg (.num 2)) QB_2_5)
def QBneg_2_4 : Expr := (.mul (.neg (.num 2)) QB_2_4)
def QBneg_2_3 : Expr := (.mul (.neg (.num 2)) QB_2_3)
def QBneg_2_2 : Expr := (.mul (.neg (.num 2)) QB_2_2)
def QBneg_2_1 : Expr := (.mul (.neg (.num 2)) QB_2_1)
def QBneg_2_0 : Expr := (.mul (.neg (.num 2)) QB_2_0)
def QBneg_1_9 : Expr := (.mul (.neg (.num 2)) QB_1_9)
def QBneg_1_8 : Expr := (.mul (.neg (.num 2)) QB_1_8)
def QBneg_1_7 : Expr := (.mul (.neg (.num 2)) QB_1_7)
def QBneg_1_6 : Expr := (.mul (.neg (.num 2)) QB_1_6)
def QBneg_1_5 : Expr := (.mul (.neg (.num 2)) QB_1_5)
def QBneg_1_4 : Expr := (.mul (.neg (.num 2)) QB_1_4)
def QBneg_1_3 : Expr := (.mul (.neg (.num 2)) QB_1_3)
def QBneg_1_2 : Expr := (.mul (.neg (.num 2)) QB_1_2)
def QBneg_1_1 : Expr := (.mul (.neg (.num 2)) QB_1_1)
def QBneg_1_0 : Expr := (.mul (.neg (.num 2)) QB_1_0)
def QBneg_0_10 : Expr := (.mul (.neg (.num 2)) QB_0_10)
def QBneg_0_9 : Expr := (.mul (.neg (.num 2)) QB_0_9)
def QBneg_0_8 : Expr := (.mul (.neg (.num 2)) QB_0_8)
def QBneg_0_7 : Expr := (.mul (.neg (.num 2)) QB_0_7)
def QBneg_0_6 : Expr := (.mul (.neg (.num 2)) QB_0_6)
def QBneg_0_5 : Expr := (.mul (.neg (.num 2)) QB_0_5)
def QBneg_0_4 : Expr := (.mul (.neg (.num 2)) QB_0_4)
def QBneg_0_3 : Expr := (.mul (.neg (.num 2)) QB_0_3)
def QBneg_0_2 : Expr := (.mul (.neg (.num 2)) QB_0_2)
def QBneg_0_1 : Expr := (.mul (.neg (.num 2)) QB_0_1)
def QBnegData : Biv := (.cons QBneg_10_0 10 0 (.cons QBneg_9_1 9 1 (.cons QBneg_9_0 9 0 (.cons QBneg_8_2 8 2 (.cons QBneg_8_1 8 1 (.cons QBneg_8_0 8 0 (.cons QBneg_7_3 7 3 (.cons QBneg_7_2 7 2 (.cons QBneg_7_1 7 1 (.cons QBneg_7_0 7 0 (.cons QBneg_6_4 6 4 (.cons QBneg_6_3 6 3 (.cons QBneg_6_2 6 2 (.cons QBneg_6_1 6 1 (.cons QBneg_6_0 6 0 (.cons QBneg_5_5 5 5 (.cons QBneg_5_4 5 4 (.cons QBneg_5_3 5 3 (.cons QBneg_5_2 5 2 (.cons QBneg_5_1 5 1 (.cons QBneg_5_0 5 0 (.cons QBneg_4_6 4 6 (.cons QBneg_4_5 4 5 (.cons QBneg_4_4 4 4 (.cons QBneg_4_3 4 3 (.cons QBneg_4_2 4 2 (.cons QBneg_4_1 4 1 (.cons QBneg_4_0 4 0 (.cons QBneg_3_7 3 7 (.cons QBneg_3_6 3 6 (.cons QBneg_3_5 3 5 (.cons QBneg_3_4 3 4 (.cons QBneg_3_3 3 3 (.cons QBneg_3_2 3 2 (.cons QBneg_3_1 3 1 (.cons QBneg_3_0 3 0 (.cons QBneg_2_8 2 8 (.cons QBneg_2_7 2 7 (.cons QBneg_2_6 2 6 (.cons QBneg_2_5 2 5 (.cons QBneg_2_4 2 4 (.cons QBneg_2_3 2 3 (.cons QBneg_2_2 2 2 (.cons QBneg_2_1 2 1 (.cons QBneg_2_0 2 0 (.cons QBneg_1_9 1 9 (.cons QBneg_1_8 1 8 (.cons QBneg_1_7 1 7 (.cons QBneg_1_6 1 6 (.cons QBneg_1_5 1 5 (.cons QBneg_1_4 1 4 (.cons QBneg_1_3 1 3 (.cons QBneg_1_2 1 2 (.cons QBneg_1_1 1 1 (.cons QBneg_1_0 1 0 (.cons QBneg_0_10 0 10 (.cons QBneg_0_9 0 9 (.cons QBneg_0_8 0 8 (.cons QBneg_0_7 0 7 (.cons QBneg_0_6 0 6 (.cons QBneg_0_5 0 5 (.cons QBneg_0_4 0 4 (.cons QBneg_0_3 0 3 (.cons QBneg_0_2 0 2 (.cons QBneg_0_1 0 1 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma QBneg_generated : scale (.neg (.num 2)) 0 0 QBData=QBnegData := by rfl
def J3_9_0 : Expr := (.mul (.num 3) J_9_0)
def J3_8_1 : Expr := (.mul (.num 3) J_8_1)
def J3_8_0 : Expr := (.mul (.num 3) J_8_0)
def J3_7_2 : Expr := (.mul (.num 3) J_7_2)
def J3_7_1 : Expr := (.mul (.num 3) J_7_1)
def J3_7_0 : Expr := (.mul (.num 3) J_7_0)
def J3_6_3 : Expr := (.mul (.num 3) J_6_3)
def J3_6_2 : Expr := (.mul (.num 3) J_6_2)
def J3_6_1 : Expr := (.mul (.num 3) J_6_1)
def J3_6_0 : Expr := (.mul (.num 3) J_6_0)
def J3_5_4 : Expr := (.mul (.num 3) J_5_4)
def J3_5_3 : Expr := (.mul (.num 3) J_5_3)
def J3_5_2 : Expr := (.mul (.num 3) J_5_2)
def J3_5_1 : Expr := (.mul (.num 3) J_5_1)
def J3_5_0 : Expr := (.mul (.num 3) J_5_0)
def J3_4_5 : Expr := (.mul (.num 3) J_4_5)
def J3_4_4 : Expr := (.mul (.num 3) J_4_4)
def J3_4_3 : Expr := (.mul (.num 3) J_4_3)
def J3_4_2 : Expr := (.mul (.num 3) J_4_2)
def J3_4_1 : Expr := (.mul (.num 3) J_4_1)
def J3_4_0 : Expr := (.mul (.num 3) J_4_0)
def J3_3_6 : Expr := (.mul (.num 3) J_3_6)
def J3_3_5 : Expr := (.mul (.num 3) J_3_5)
def J3_3_4 : Expr := (.mul (.num 3) J_3_4)
def J3_3_3 : Expr := (.mul (.num 3) J_3_3)
def J3_3_2 : Expr := (.mul (.num 3) J_3_2)
def J3_3_1 : Expr := (.mul (.num 3) J_3_1)
def J3_3_0 : Expr := (.mul (.num 3) J_3_0)
def J3_2_7 : Expr := (.mul (.num 3) J_2_7)
def J3_2_6 : Expr := (.mul (.num 3) J_2_6)
def J3_2_5 : Expr := (.mul (.num 3) J_2_5)
def J3_2_4 : Expr := (.mul (.num 3) J_2_4)
def J3_2_3 : Expr := (.mul (.num 3) J_2_3)
def J3_2_2 : Expr := (.mul (.num 3) J_2_2)
def J3_2_1 : Expr := (.mul (.num 3) J_2_1)
def J3_2_0 : Expr := (.mul (.num 3) J_2_0)
def J3_1_8 : Expr := (.mul (.num 3) J_1_8)
def J3_1_7 : Expr := (.mul (.num 3) J_1_7)
def J3_1_6 : Expr := (.mul (.num 3) J_1_6)
def J3_1_5 : Expr := (.mul (.num 3) J_1_5)
def J3_1_4 : Expr := (.mul (.num 3) J_1_4)
def J3_1_3 : Expr := (.mul (.num 3) J_1_3)
def J3_1_2 : Expr := (.mul (.num 3) J_1_2)
def J3_1_1 : Expr := (.mul (.num 3) J_1_1)
def J3_1_0 : Expr := (.mul (.num 3) J_1_0)
def J3_0_9 : Expr := (.mul (.num 3) J_0_9)
def J3_0_8 : Expr := (.mul (.num 3) J_0_8)
def J3_0_7 : Expr := (.mul (.num 3) J_0_7)
def J3_0_6 : Expr := (.mul (.num 3) J_0_6)
def J3_0_5 : Expr := (.mul (.num 3) J_0_5)
def J3_0_4 : Expr := (.mul (.num 3) J_0_4)
def J3_0_3 : Expr := (.mul (.num 3) J_0_3)
def J3_0_2 : Expr := (.mul (.num 3) J_0_2)
def J3_0_1 : Expr := (.mul (.num 3) J_0_1)
def J3_0_0 : Expr := (.mul (.num 3) J_0_0)
def J3Data : Biv := (.cons J3_9_0 9 0 (.cons J3_8_1 8 1 (.cons J3_8_0 8 0 (.cons J3_7_2 7 2 (.cons J3_7_1 7 1 (.cons J3_7_0 7 0 (.cons J3_6_3 6 3 (.cons J3_6_2 6 2 (.cons J3_6_1 6 1 (.cons J3_6_0 6 0 (.cons J3_5_4 5 4 (.cons J3_5_3 5 3 (.cons J3_5_2 5 2 (.cons J3_5_1 5 1 (.cons J3_5_0 5 0 (.cons J3_4_5 4 5 (.cons J3_4_4 4 4 (.cons J3_4_3 4 3 (.cons J3_4_2 4 2 (.cons J3_4_1 4 1 (.cons J3_4_0 4 0 (.cons J3_3_6 3 6 (.cons J3_3_5 3 5 (.cons J3_3_4 3 4 (.cons J3_3_3 3 3 (.cons J3_3_2 3 2 (.cons J3_3_1 3 1 (.cons J3_3_0 3 0 (.cons J3_2_7 2 7 (.cons J3_2_6 2 6 (.cons J3_2_5 2 5 (.cons J3_2_4 2 4 (.cons J3_2_3 2 3 (.cons J3_2_2 2 2 (.cons J3_2_1 2 1 (.cons J3_2_0 2 0 (.cons J3_1_8 1 8 (.cons J3_1_7 1 7 (.cons J3_1_6 1 6 (.cons J3_1_5 1 5 (.cons J3_1_4 1 4 (.cons J3_1_3 1 3 (.cons J3_1_2 1 2 (.cons J3_1_1 1 1 (.cons J3_1_0 1 0 (.cons J3_0_9 0 9 (.cons J3_0_8 0 8 (.cons J3_0_7 0 7 (.cons J3_0_6 0 6 (.cons J3_0_5 0 5 (.cons J3_0_4 0 4 (.cons J3_0_3 0 3 (.cons J3_0_2 0 2 (.cons J3_0_1 0 1 (.cons J3_0_0 0 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma J3_generated : scale (.num 3) 0 0 JData=J3Data := by rfl
def Left0_10_0 : Expr := (.add HA_10_0 QBneg_10_0)
def Left0_9_1 : Expr := (.add HA_9_1 QBneg_9_1)
def Left0_9_0 : Expr := (.add HA_9_0 QBneg_9_0)
def Left0_8_2 : Expr := (.add HA_8_2 QBneg_8_2)
def Left0_8_1 : Expr := (.add HA_8_1 QBneg_8_1)
def Left0_8_0 : Expr := (.add HA_8_0 QBneg_8_0)
def Left0_7_3 : Expr := (.add HA_7_3 QBneg_7_3)
def Left0_7_2 : Expr := (.add HA_7_2 QBneg_7_2)
def Left0_7_1 : Expr := (.add HA_7_1 QBneg_7_1)
def Left0_7_0 : Expr := (.add HA_7_0 QBneg_7_0)
def Left0_6_4 : Expr := (.add HA_6_4 QBneg_6_4)
def Left0_6_3 : Expr := (.add HA_6_3 QBneg_6_3)
def Left0_6_2 : Expr := (.add HA_6_2 QBneg_6_2)
def Left0_6_1 : Expr := (.add HA_6_1 QBneg_6_1)
def Left0_6_0 : Expr := (.add HA_6_0 QBneg_6_0)
def Left0_5_5 : Expr := (.add HA_5_5 QBneg_5_5)
def Left0_5_4 : Expr := (.add HA_5_4 QBneg_5_4)
def Left0_5_3 : Expr := (.add HA_5_3 QBneg_5_3)
def Left0_5_2 : Expr := (.add HA_5_2 QBneg_5_2)
def Left0_5_1 : Expr := (.add HA_5_1 QBneg_5_1)
def Left0_5_0 : Expr := (.add HA_5_0 QBneg_5_0)
def Left0_4_6 : Expr := (.add HA_4_6 QBneg_4_6)
def Left0_4_5 : Expr := (.add HA_4_5 QBneg_4_5)
def Left0_4_4 : Expr := (.add HA_4_4 QBneg_4_4)
def Left0_4_3 : Expr := (.add HA_4_3 QBneg_4_3)
def Left0_4_2 : Expr := (.add HA_4_2 QBneg_4_2)
def Left0_4_1 : Expr := (.add HA_4_1 QBneg_4_1)
def Left0_4_0 : Expr := (.add HA_4_0 QBneg_4_0)
def Left0_3_7 : Expr := (.add HA_3_7 QBneg_3_7)
def Left0_3_6 : Expr := (.add HA_3_6 QBneg_3_6)
def Left0_3_5 : Expr := (.add HA_3_5 QBneg_3_5)
def Left0_3_4 : Expr := (.add HA_3_4 QBneg_3_4)
def Left0_3_3 : Expr := (.add HA_3_3 QBneg_3_3)
def Left0_3_2 : Expr := (.add HA_3_2 QBneg_3_2)
def Left0_3_1 : Expr := (.add HA_3_1 QBneg_3_1)
def Left0_3_0 : Expr := (.add HA_3_0 QBneg_3_0)
def Left0_2_8 : Expr := (.add HA_2_8 QBneg_2_8)
def Left0_2_7 : Expr := (.add HA_2_7 QBneg_2_7)
def Left0_2_6 : Expr := (.add HA_2_6 QBneg_2_6)
def Left0_2_5 : Expr := (.add HA_2_5 QBneg_2_5)
def Left0_2_4 : Expr := (.add HA_2_4 QBneg_2_4)
def Left0_2_3 : Expr := (.add HA_2_3 QBneg_2_3)
def Left0_2_2 : Expr := (.add HA_2_2 QBneg_2_2)
def Left0_2_1 : Expr := (.add HA_2_1 QBneg_2_1)
def Left0_2_0 : Expr := (.add HA_2_0 QBneg_2_0)
def Left0_1_9 : Expr := (.add HA_1_9 QBneg_1_9)
def Left0_1_8 : Expr := (.add HA_1_8 QBneg_1_8)
def Left0_1_7 : Expr := (.add HA_1_7 QBneg_1_7)
def Left0_1_6 : Expr := (.add HA_1_6 QBneg_1_6)
def Left0_1_5 : Expr := (.add HA_1_5 QBneg_1_5)
def Left0_1_4 : Expr := (.add HA_1_4 QBneg_1_4)
def Left0_1_3 : Expr := (.add HA_1_3 QBneg_1_3)
def Left0_1_2 : Expr := (.add HA_1_2 QBneg_1_2)
def Left0_1_1 : Expr := (.add HA_1_1 QBneg_1_1)
def Left0_1_0 : Expr := (.add HA_1_0 QBneg_1_0)
def Left0_0_10 : Expr := (.add HA_0_10 QBneg_0_10)
def Left0_0_9 : Expr := (.add HA_0_9 QBneg_0_9)
def Left0_0_8 : Expr := (.add HA_0_8 QBneg_0_8)
def Left0_0_7 : Expr := (.add HA_0_7 QBneg_0_7)
def Left0_0_6 : Expr := (.add HA_0_6 QBneg_0_6)
def Left0_0_5 : Expr := (.add HA_0_5 QBneg_0_5)
def Left0_0_4 : Expr := (.add HA_0_4 QBneg_0_4)
def Left0_0_3 : Expr := (.add HA_0_3 QBneg_0_3)
def Left0_0_2 : Expr := (.add HA_0_2 QBneg_0_2)
def Left0_0_1 : Expr := (.add HA_0_1 QBneg_0_1)
def Left0Data : Biv := (.cons Left0_10_0 10 0 (.cons Left0_9_1 9 1 (.cons Left0_9_0 9 0 (.cons Left0_8_2 8 2 (.cons Left0_8_1 8 1 (.cons Left0_8_0 8 0 (.cons Left0_7_3 7 3 (.cons Left0_7_2 7 2 (.cons Left0_7_1 7 1 (.cons Left0_7_0 7 0 (.cons Left0_6_4 6 4 (.cons Left0_6_3 6 3 (.cons Left0_6_2 6 2 (.cons Left0_6_1 6 1 (.cons Left0_6_0 6 0 (.cons Left0_5_5 5 5 (.cons Left0_5_4 5 4 (.cons Left0_5_3 5 3 (.cons Left0_5_2 5 2 (.cons Left0_5_1 5 1 (.cons Left0_5_0 5 0 (.cons Left0_4_6 4 6 (.cons Left0_4_5 4 5 (.cons Left0_4_4 4 4 (.cons Left0_4_3 4 3 (.cons Left0_4_2 4 2 (.cons Left0_4_1 4 1 (.cons Left0_4_0 4 0 (.cons Left0_3_7 3 7 (.cons Left0_3_6 3 6 (.cons Left0_3_5 3 5 (.cons Left0_3_4 3 4 (.cons Left0_3_3 3 3 (.cons Left0_3_2 3 2 (.cons Left0_3_1 3 1 (.cons Left0_3_0 3 0 (.cons Left0_2_8 2 8 (.cons Left0_2_7 2 7 (.cons Left0_2_6 2 6 (.cons Left0_2_5 2 5 (.cons Left0_2_4 2 4 (.cons Left0_2_3 2 3 (.cons Left0_2_2 2 2 (.cons Left0_2_1 2 1 (.cons Left0_2_0 2 0 (.cons Left0_1_9 1 9 (.cons Left0_1_8 1 8 (.cons Left0_1_7 1 7 (.cons Left0_1_6 1 6 (.cons Left0_1_5 1 5 (.cons Left0_1_4 1 4 (.cons Left0_1_3 1 3 (.cons Left0_1_2 1 2 (.cons Left0_1_1 1 1 (.cons Left0_1_0 1 0 (.cons Left0_0_10 0 10 (.cons Left0_0_9 0 9 (.cons Left0_0_8 0 8 (.cons Left0_0_7 0 7 (.cons Left0_0_6 0 6 (.cons Left0_0_5 0 5 (.cons Left0_0_4 0 4 (.cons Left0_0_3 0 3 (.cons Left0_0_2 0 2 (.cons Left0_0_1 0 1 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma Left0_generated : merge 512 HAData QBnegData=Left0Data := by rfl
def Left_10_0 : Expr := Left0_10_0
def Left_9_1 : Expr := Left0_9_1
def Left_9_0 : Expr := (.add Left0_9_0 J3_9_0)
def Left_8_2 : Expr := Left0_8_2
def Left_8_1 : Expr := (.add Left0_8_1 J3_8_1)
def Left_8_0 : Expr := (.add Left0_8_0 J3_8_0)
def Left_7_3 : Expr := Left0_7_3
def Left_7_2 : Expr := (.add Left0_7_2 J3_7_2)
def Left_7_1 : Expr := (.add Left0_7_1 J3_7_1)
def Left_7_0 : Expr := (.add Left0_7_0 J3_7_0)
def Left_6_4 : Expr := Left0_6_4
def Left_6_3 : Expr := (.add Left0_6_3 J3_6_3)
def Left_6_2 : Expr := (.add Left0_6_2 J3_6_2)
def Left_6_1 : Expr := (.add Left0_6_1 J3_6_1)
def Left_6_0 : Expr := (.add Left0_6_0 J3_6_0)
def Left_5_5 : Expr := Left0_5_5
def Left_5_4 : Expr := (.add Left0_5_4 J3_5_4)
def Left_5_3 : Expr := (.add Left0_5_3 J3_5_3)
def Left_5_2 : Expr := (.add Left0_5_2 J3_5_2)
def Left_5_1 : Expr := (.add Left0_5_1 J3_5_1)
def Left_5_0 : Expr := (.add Left0_5_0 J3_5_0)
def Left_4_6 : Expr := Left0_4_6
def Left_4_5 : Expr := (.add Left0_4_5 J3_4_5)
def Left_4_4 : Expr := (.add Left0_4_4 J3_4_4)
def Left_4_3 : Expr := (.add Left0_4_3 J3_4_3)
def Left_4_2 : Expr := (.add Left0_4_2 J3_4_2)
def Left_4_1 : Expr := (.add Left0_4_1 J3_4_1)
def Left_4_0 : Expr := (.add Left0_4_0 J3_4_0)
def Left_3_7 : Expr := Left0_3_7
def Left_3_6 : Expr := (.add Left0_3_6 J3_3_6)
def Left_3_5 : Expr := (.add Left0_3_5 J3_3_5)
def Left_3_4 : Expr := (.add Left0_3_4 J3_3_4)
def Left_3_3 : Expr := (.add Left0_3_3 J3_3_3)
def Left_3_2 : Expr := (.add Left0_3_2 J3_3_2)
def Left_3_1 : Expr := (.add Left0_3_1 J3_3_1)
def Left_3_0 : Expr := (.add Left0_3_0 J3_3_0)
def Left_2_8 : Expr := Left0_2_8
def Left_2_7 : Expr := (.add Left0_2_7 J3_2_7)
def Left_2_6 : Expr := (.add Left0_2_6 J3_2_6)
def Left_2_5 : Expr := (.add Left0_2_5 J3_2_5)
def Left_2_4 : Expr := (.add Left0_2_4 J3_2_4)
def Left_2_3 : Expr := (.add Left0_2_3 J3_2_3)
def Left_2_2 : Expr := (.add Left0_2_2 J3_2_2)
def Left_2_1 : Expr := (.add Left0_2_1 J3_2_1)
def Left_2_0 : Expr := (.add Left0_2_0 J3_2_0)
def Left_1_9 : Expr := Left0_1_9
def Left_1_8 : Expr := (.add Left0_1_8 J3_1_8)
def Left_1_7 : Expr := (.add Left0_1_7 J3_1_7)
def Left_1_6 : Expr := (.add Left0_1_6 J3_1_6)
def Left_1_5 : Expr := (.add Left0_1_5 J3_1_5)
def Left_1_4 : Expr := (.add Left0_1_4 J3_1_4)
def Left_1_3 : Expr := (.add Left0_1_3 J3_1_3)
def Left_1_2 : Expr := (.add Left0_1_2 J3_1_2)
def Left_1_1 : Expr := (.add Left0_1_1 J3_1_1)
def Left_1_0 : Expr := (.add Left0_1_0 J3_1_0)
def Left_0_10 : Expr := Left0_0_10
def Left_0_9 : Expr := (.add Left0_0_9 J3_0_9)
def Left_0_8 : Expr := (.add Left0_0_8 J3_0_8)
def Left_0_7 : Expr := (.add Left0_0_7 J3_0_7)
def Left_0_6 : Expr := (.add Left0_0_6 J3_0_6)
def Left_0_5 : Expr := (.add Left0_0_5 J3_0_5)
def Left_0_4 : Expr := (.add Left0_0_4 J3_0_4)
def Left_0_3 : Expr := (.add Left0_0_3 J3_0_3)
def Left_0_2 : Expr := (.add Left0_0_2 J3_0_2)
def Left_0_1 : Expr := (.add Left0_0_1 J3_0_1)
def Left_0_0 : Expr := J3_0_0
def LeftData : Biv := (.cons Left_10_0 10 0 (.cons Left_9_1 9 1 (.cons Left_9_0 9 0 (.cons Left_8_2 8 2 (.cons Left_8_1 8 1 (.cons Left_8_0 8 0 (.cons Left_7_3 7 3 (.cons Left_7_2 7 2 (.cons Left_7_1 7 1 (.cons Left_7_0 7 0 (.cons Left_6_4 6 4 (.cons Left_6_3 6 3 (.cons Left_6_2 6 2 (.cons Left_6_1 6 1 (.cons Left_6_0 6 0 (.cons Left_5_5 5 5 (.cons Left_5_4 5 4 (.cons Left_5_3 5 3 (.cons Left_5_2 5 2 (.cons Left_5_1 5 1 (.cons Left_5_0 5 0 (.cons Left_4_6 4 6 (.cons Left_4_5 4 5 (.cons Left_4_4 4 4 (.cons Left_4_3 4 3 (.cons Left_4_2 4 2 (.cons Left_4_1 4 1 (.cons Left_4_0 4 0 (.cons Left_3_7 3 7 (.cons Left_3_6 3 6 (.cons Left_3_5 3 5 (.cons Left_3_4 3 4 (.cons Left_3_3 3 3 (.cons Left_3_2 3 2 (.cons Left_3_1 3 1 (.cons Left_3_0 3 0 (.cons Left_2_8 2 8 (.cons Left_2_7 2 7 (.cons Left_2_6 2 6 (.cons Left_2_5 2 5 (.cons Left_2_4 2 4 (.cons Left_2_3 2 3 (.cons Left_2_2 2 2 (.cons Left_2_1 2 1 (.cons Left_2_0 2 0 (.cons Left_1_9 1 9 (.cons Left_1_8 1 8 (.cons Left_1_7 1 7 (.cons Left_1_6 1 6 (.cons Left_1_5 1 5 (.cons Left_1_4 1 4 (.cons Left_1_3 1 3 (.cons Left_1_2 1 2 (.cons Left_1_1 1 1 (.cons Left_1_0 1 0 (.cons Left_0_10 0 10 (.cons Left_0_9 0 9 (.cons Left_0_8 0 8 (.cons Left_0_7 0 7 (.cons Left_0_6 0 6 (.cons Left_0_5 0 5 (.cons Left_0_4 0 4 (.cons Left_0_3 0 3 (.cons Left_0_2 0 2 (.cons Left_0_1 0 1 (.cons Left_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma Left_generated : merge 512 Left0Data J3Data=LeftData := by rfl
def C0_7_0 : Expr := (.mul Hx_2_0 Thetay_5_0)
def C0_6_1 : Expr := (.add (.mul Hx_2_0 Thetay_4_1) (.mul Hx_1_1 Thetay_5_0))
def C0_6_0 : Expr := (.add (.mul Hx_2_0 Thetay_4_0) (.mul Hx_1_0 Thetay_5_0))
def C0_5_2 : Expr := (.add (.mul Hx_2_0 Thetay_3_2) (.add (.mul Hx_1_1 Thetay_4_1) (.mul Hx_0_2 Thetay_5_0)))
def C0_5_1 : Expr := (.add (.mul Hx_2_0 Thetay_3_1) (.add (.mul Hx_1_1 Thetay_4_0) (.add (.mul Hx_1_0 Thetay_4_1) (.mul Hx_0_1 Thetay_5_0))))
def C0_5_0 : Expr := (.add (.mul Hx_2_0 Thetay_3_0) (.add (.mul Hx_1_0 Thetay_4_0) (.mul Hx_0_0 Thetay_5_0)))
def C0_4_3 : Expr := (.add (.mul Hx_2_0 Thetay_2_3) (.add (.mul Hx_1_1 Thetay_3_2) (.mul Hx_0_2 Thetay_4_1)))
def C0_4_2 : Expr := (.add (.mul Hx_2_0 Thetay_2_2) (.add (.mul Hx_1_1 Thetay_3_1) (.add (.mul Hx_1_0 Thetay_3_2) (.add (.mul Hx_0_2 Thetay_4_0) (.mul Hx_0_1 Thetay_4_1)))))
def C0_4_1 : Expr := (.add (.mul Hx_2_0 Thetay_2_1) (.add (.mul Hx_1_1 Thetay_3_0) (.add (.mul Hx_1_0 Thetay_3_1) (.add (.mul Hx_0_1 Thetay_4_0) (.mul Hx_0_0 Thetay_4_1)))))
def C0_4_0 : Expr := (.add (.mul Hx_2_0 Thetay_2_0) (.add (.mul Hx_1_0 Thetay_3_0) (.mul Hx_0_0 Thetay_4_0)))
def C0_3_4 : Expr := (.add (.mul Hx_2_0 Thetay_1_4) (.add (.mul Hx_1_1 Thetay_2_3) (.mul Hx_0_2 Thetay_3_2)))
def C0_3_3 : Expr := (.add (.mul Hx_2_0 Thetay_1_3) (.add (.mul Hx_1_1 Thetay_2_2) (.add (.mul Hx_1_0 Thetay_2_3) (.add (.mul Hx_0_2 Thetay_3_1) (.mul Hx_0_1 Thetay_3_2)))))
def C0_3_2 : Expr := (.add (.mul Hx_2_0 Thetay_1_2) (.add (.mul Hx_1_1 Thetay_2_1) (.add (.mul Hx_1_0 Thetay_2_2) (.add (.mul Hx_0_2 Thetay_3_0) (.add (.mul Hx_0_1 Thetay_3_1) (.mul Hx_0_0 Thetay_3_2))))))
def C0_3_1 : Expr := (.add (.mul Hx_2_0 Thetay_1_1) (.add (.mul Hx_1_1 Thetay_2_0) (.add (.mul Hx_1_0 Thetay_2_1) (.add (.mul Hx_0_1 Thetay_3_0) (.mul Hx_0_0 Thetay_3_1)))))
def C0_3_0 : Expr := (.add (.mul Hx_2_0 Thetay_1_0) (.add (.mul Hx_1_0 Thetay_2_0) (.mul Hx_0_0 Thetay_3_0)))
def C0_2_5 : Expr := (.add (.mul Hx_2_0 Thetay_0_5) (.add (.mul Hx_1_1 Thetay_1_4) (.mul Hx_0_2 Thetay_2_3)))
def C0_2_4 : Expr := (.add (.mul Hx_2_0 Thetay_0_4) (.add (.mul Hx_1_1 Thetay_1_3) (.add (.mul Hx_1_0 Thetay_1_4) (.add (.mul Hx_0_2 Thetay_2_2) (.mul Hx_0_1 Thetay_2_3)))))
def C0_2_3 : Expr := (.add (.mul Hx_2_0 Thetay_0_3) (.add (.mul Hx_1_1 Thetay_1_2) (.add (.mul Hx_1_0 Thetay_1_3) (.add (.mul Hx_0_2 Thetay_2_1) (.add (.mul Hx_0_1 Thetay_2_2) (.mul Hx_0_0 Thetay_2_3))))))
def C0_2_2 : Expr := (.add (.mul Hx_2_0 Thetay_0_2) (.add (.mul Hx_1_1 Thetay_1_1) (.add (.mul Hx_1_0 Thetay_1_2) (.add (.mul Hx_0_2 Thetay_2_0) (.add (.mul Hx_0_1 Thetay_2_1) (.mul Hx_0_0 Thetay_2_2))))))
def C0_2_1 : Expr := (.add (.mul Hx_2_0 Thetay_0_1) (.add (.mul Hx_1_1 Thetay_1_0) (.add (.mul Hx_1_0 Thetay_1_1) (.add (.mul Hx_0_1 Thetay_2_0) (.mul Hx_0_0 Thetay_2_1)))))
def C0_2_0 : Expr := (.add (.mul Hx_2_0 Thetay_0_0) (.add (.mul Hx_1_0 Thetay_1_0) (.mul Hx_0_0 Thetay_2_0)))
def C0_1_6 : Expr := (.add (.mul Hx_1_1 Thetay_0_5) (.mul Hx_0_2 Thetay_1_4))
def C0_1_5 : Expr := (.add (.mul Hx_1_1 Thetay_0_4) (.add (.mul Hx_1_0 Thetay_0_5) (.add (.mul Hx_0_2 Thetay_1_3) (.mul Hx_0_1 Thetay_1_4))))
def C0_1_4 : Expr := (.add (.mul Hx_1_1 Thetay_0_3) (.add (.mul Hx_1_0 Thetay_0_4) (.add (.mul Hx_0_2 Thetay_1_2) (.add (.mul Hx_0_1 Thetay_1_3) (.mul Hx_0_0 Thetay_1_4)))))
def C0_1_3 : Expr := (.add (.mul Hx_1_1 Thetay_0_2) (.add (.mul Hx_1_0 Thetay_0_3) (.add (.mul Hx_0_2 Thetay_1_1) (.add (.mul Hx_0_1 Thetay_1_2) (.mul Hx_0_0 Thetay_1_3)))))
def C0_1_2 : Expr := (.add (.mul Hx_1_1 Thetay_0_1) (.add (.mul Hx_1_0 Thetay_0_2) (.add (.mul Hx_0_2 Thetay_1_0) (.add (.mul Hx_0_1 Thetay_1_1) (.mul Hx_0_0 Thetay_1_2)))))
def C0_1_1 : Expr := (.add (.mul Hx_1_1 Thetay_0_0) (.add (.mul Hx_1_0 Thetay_0_1) (.add (.mul Hx_0_1 Thetay_1_0) (.mul Hx_0_0 Thetay_1_1))))
def C0_1_0 : Expr := (.add (.mul Hx_1_0 Thetay_0_0) (.mul Hx_0_0 Thetay_1_0))
def C0_0_7 : Expr := (.mul Hx_0_2 Thetay_0_5)
def C0_0_6 : Expr := (.add (.mul Hx_0_2 Thetay_0_4) (.mul Hx_0_1 Thetay_0_5))
def C0_0_5 : Expr := (.add (.mul Hx_0_2 Thetay_0_3) (.add (.mul Hx_0_1 Thetay_0_4) (.mul Hx_0_0 Thetay_0_5)))
def C0_0_4 : Expr := (.add (.mul Hx_0_2 Thetay_0_2) (.add (.mul Hx_0_1 Thetay_0_3) (.mul Hx_0_0 Thetay_0_4)))
def C0_0_3 : Expr := (.add (.mul Hx_0_2 Thetay_0_1) (.add (.mul Hx_0_1 Thetay_0_2) (.mul Hx_0_0 Thetay_0_3)))
def C0_0_2 : Expr := (.add (.mul Hx_0_2 Thetay_0_0) (.add (.mul Hx_0_1 Thetay_0_1) (.mul Hx_0_0 Thetay_0_2)))
def C0_0_1 : Expr := (.add (.mul Hx_0_1 Thetay_0_0) (.mul Hx_0_0 Thetay_0_1))
def C0_0_0 : Expr := (.mul Hx_0_0 Thetay_0_0)
def C0Data : Biv := (.cons C0_7_0 7 0 (.cons C0_6_1 6 1 (.cons C0_6_0 6 0 (.cons C0_5_2 5 2 (.cons C0_5_1 5 1 (.cons C0_5_0 5 0 (.cons C0_4_3 4 3 (.cons C0_4_2 4 2 (.cons C0_4_1 4 1 (.cons C0_4_0 4 0 (.cons C0_3_4 3 4 (.cons C0_3_3 3 3 (.cons C0_3_2 3 2 (.cons C0_3_1 3 1 (.cons C0_3_0 3 0 (.cons C0_2_5 2 5 (.cons C0_2_4 2 4 (.cons C0_2_3 2 3 (.cons C0_2_2 2 2 (.cons C0_2_1 2 1 (.cons C0_2_0 2 0 (.cons C0_1_6 1 6 (.cons C0_1_5 1 5 (.cons C0_1_4 1 4 (.cons C0_1_3 1 3 (.cons C0_1_2 1 2 (.cons C0_1_1 1 1 (.cons C0_1_0 1 0 (.cons C0_0_7 0 7 (.cons C0_0_6 0 6 (.cons C0_0_5 0 5 (.cons C0_0_4 0 4 (.cons C0_0_3 0 3 (.cons C0_0_2 0 2 (.cons C0_0_1 0 1 (.cons C0_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))
lemma C0_generated : multiply HxData ThetayData=C0Data := by rfl
def C1_7_0 : Expr := (.mul Hy_2_0 Thetax_5_0)
def C1_6_1 : Expr := (.add (.mul Hy_2_0 Thetax_4_1) (.mul Hy_1_1 Thetax_5_0))
def C1_6_0 : Expr := (.add (.mul Hy_2_0 Thetax_4_0) (.mul Hy_1_0 Thetax_5_0))
def C1_5_2 : Expr := (.add (.mul Hy_2_0 Thetax_3_2) (.add (.mul Hy_1_1 Thetax_4_1) (.mul Hy_0_2 Thetax_5_0)))
def C1_5_1 : Expr := (.add (.mul Hy_2_0 Thetax_3_1) (.add (.mul Hy_1_1 Thetax_4_0) (.add (.mul Hy_1_0 Thetax_4_1) (.mul Hy_0_1 Thetax_5_0))))
def C1_5_0 : Expr := (.add (.mul Hy_2_0 Thetax_3_0) (.add (.mul Hy_1_0 Thetax_4_0) (.mul Hy_0_0 Thetax_5_0)))
def C1_4_3 : Expr := (.add (.mul Hy_2_0 Thetax_2_3) (.add (.mul Hy_1_1 Thetax_3_2) (.mul Hy_0_2 Thetax_4_1)))
def C1_4_2 : Expr := (.add (.mul Hy_2_0 Thetax_2_2) (.add (.mul Hy_1_1 Thetax_3_1) (.add (.mul Hy_1_0 Thetax_3_2) (.add (.mul Hy_0_2 Thetax_4_0) (.mul Hy_0_1 Thetax_4_1)))))
def C1_4_1 : Expr := (.add (.mul Hy_2_0 Thetax_2_1) (.add (.mul Hy_1_1 Thetax_3_0) (.add (.mul Hy_1_0 Thetax_3_1) (.add (.mul Hy_0_1 Thetax_4_0) (.mul Hy_0_0 Thetax_4_1)))))
def C1_4_0 : Expr := (.add (.mul Hy_2_0 Thetax_2_0) (.add (.mul Hy_1_0 Thetax_3_0) (.mul Hy_0_0 Thetax_4_0)))
def C1_3_4 : Expr := (.add (.mul Hy_2_0 Thetax_1_4) (.add (.mul Hy_1_1 Thetax_2_3) (.mul Hy_0_2 Thetax_3_2)))
def C1_3_3 : Expr := (.add (.mul Hy_2_0 Thetax_1_3) (.add (.mul Hy_1_1 Thetax_2_2) (.add (.mul Hy_1_0 Thetax_2_3) (.add (.mul Hy_0_2 Thetax_3_1) (.mul Hy_0_1 Thetax_3_2)))))
def C1_3_2 : Expr := (.add (.mul Hy_2_0 Thetax_1_2) (.add (.mul Hy_1_1 Thetax_2_1) (.add (.mul Hy_1_0 Thetax_2_2) (.add (.mul Hy_0_2 Thetax_3_0) (.add (.mul Hy_0_1 Thetax_3_1) (.mul Hy_0_0 Thetax_3_2))))))
def C1_3_1 : Expr := (.add (.mul Hy_2_0 Thetax_1_1) (.add (.mul Hy_1_1 Thetax_2_0) (.add (.mul Hy_1_0 Thetax_2_1) (.add (.mul Hy_0_1 Thetax_3_0) (.mul Hy_0_0 Thetax_3_1)))))
def C1_3_0 : Expr := (.add (.mul Hy_2_0 Thetax_1_0) (.add (.mul Hy_1_0 Thetax_2_0) (.mul Hy_0_0 Thetax_3_0)))
def C1_2_5 : Expr := (.add (.mul Hy_2_0 Thetax_0_5) (.add (.mul Hy_1_1 Thetax_1_4) (.mul Hy_0_2 Thetax_2_3)))
def C1_2_4 : Expr := (.add (.mul Hy_2_0 Thetax_0_4) (.add (.mul Hy_1_1 Thetax_1_3) (.add (.mul Hy_1_0 Thetax_1_4) (.add (.mul Hy_0_2 Thetax_2_2) (.mul Hy_0_1 Thetax_2_3)))))
def C1_2_3 : Expr := (.add (.mul Hy_2_0 Thetax_0_3) (.add (.mul Hy_1_1 Thetax_1_2) (.add (.mul Hy_1_0 Thetax_1_3) (.add (.mul Hy_0_2 Thetax_2_1) (.add (.mul Hy_0_1 Thetax_2_2) (.mul Hy_0_0 Thetax_2_3))))))
def C1_2_2 : Expr := (.add (.mul Hy_2_0 Thetax_0_2) (.add (.mul Hy_1_1 Thetax_1_1) (.add (.mul Hy_1_0 Thetax_1_2) (.add (.mul Hy_0_2 Thetax_2_0) (.add (.mul Hy_0_1 Thetax_2_1) (.mul Hy_0_0 Thetax_2_2))))))
def C1_2_1 : Expr := (.add (.mul Hy_2_0 Thetax_0_1) (.add (.mul Hy_1_1 Thetax_1_0) (.add (.mul Hy_1_0 Thetax_1_1) (.add (.mul Hy_0_1 Thetax_2_0) (.mul Hy_0_0 Thetax_2_1)))))
def C1_2_0 : Expr := (.add (.mul Hy_2_0 Thetax_0_0) (.add (.mul Hy_1_0 Thetax_1_0) (.mul Hy_0_0 Thetax_2_0)))
def C1_1_6 : Expr := (.add (.mul Hy_1_1 Thetax_0_5) (.mul Hy_0_2 Thetax_1_4))
def C1_1_5 : Expr := (.add (.mul Hy_1_1 Thetax_0_4) (.add (.mul Hy_1_0 Thetax_0_5) (.add (.mul Hy_0_2 Thetax_1_3) (.mul Hy_0_1 Thetax_1_4))))
def C1_1_4 : Expr := (.add (.mul Hy_1_1 Thetax_0_3) (.add (.mul Hy_1_0 Thetax_0_4) (.add (.mul Hy_0_2 Thetax_1_2) (.add (.mul Hy_0_1 Thetax_1_3) (.mul Hy_0_0 Thetax_1_4)))))
def C1_1_3 : Expr := (.add (.mul Hy_1_1 Thetax_0_2) (.add (.mul Hy_1_0 Thetax_0_3) (.add (.mul Hy_0_2 Thetax_1_1) (.add (.mul Hy_0_1 Thetax_1_2) (.mul Hy_0_0 Thetax_1_3)))))
def C1_1_2 : Expr := (.add (.mul Hy_1_1 Thetax_0_1) (.add (.mul Hy_1_0 Thetax_0_2) (.add (.mul Hy_0_2 Thetax_1_0) (.add (.mul Hy_0_1 Thetax_1_1) (.mul Hy_0_0 Thetax_1_2)))))
def C1_1_1 : Expr := (.add (.mul Hy_1_1 Thetax_0_0) (.add (.mul Hy_1_0 Thetax_0_1) (.add (.mul Hy_0_1 Thetax_1_0) (.mul Hy_0_0 Thetax_1_1))))
def C1_1_0 : Expr := (.add (.mul Hy_1_0 Thetax_0_0) (.mul Hy_0_0 Thetax_1_0))
def C1_0_7 : Expr := (.mul Hy_0_2 Thetax_0_5)
def C1_0_6 : Expr := (.add (.mul Hy_0_2 Thetax_0_4) (.mul Hy_0_1 Thetax_0_5))
def C1_0_5 : Expr := (.add (.mul Hy_0_2 Thetax_0_3) (.add (.mul Hy_0_1 Thetax_0_4) (.mul Hy_0_0 Thetax_0_5)))
def C1_0_4 : Expr := (.add (.mul Hy_0_2 Thetax_0_2) (.add (.mul Hy_0_1 Thetax_0_3) (.mul Hy_0_0 Thetax_0_4)))
def C1_0_3 : Expr := (.add (.mul Hy_0_2 Thetax_0_1) (.add (.mul Hy_0_1 Thetax_0_2) (.mul Hy_0_0 Thetax_0_3)))
def C1_0_2 : Expr := (.add (.mul Hy_0_2 Thetax_0_0) (.add (.mul Hy_0_1 Thetax_0_1) (.mul Hy_0_0 Thetax_0_2)))
def C1_0_1 : Expr := (.add (.mul Hy_0_1 Thetax_0_0) (.mul Hy_0_0 Thetax_0_1))
def C1_0_0 : Expr := (.mul Hy_0_0 Thetax_0_0)
def C1Data : Biv := (.cons C1_7_0 7 0 (.cons C1_6_1 6 1 (.cons C1_6_0 6 0 (.cons C1_5_2 5 2 (.cons C1_5_1 5 1 (.cons C1_5_0 5 0 (.cons C1_4_3 4 3 (.cons C1_4_2 4 2 (.cons C1_4_1 4 1 (.cons C1_4_0 4 0 (.cons C1_3_4 3 4 (.cons C1_3_3 3 3 (.cons C1_3_2 3 2 (.cons C1_3_1 3 1 (.cons C1_3_0 3 0 (.cons C1_2_5 2 5 (.cons C1_2_4 2 4 (.cons C1_2_3 2 3 (.cons C1_2_2 2 2 (.cons C1_2_1 2 1 (.cons C1_2_0 2 0 (.cons C1_1_6 1 6 (.cons C1_1_5 1 5 (.cons C1_1_4 1 4 (.cons C1_1_3 1 3 (.cons C1_1_2 1 2 (.cons C1_1_1 1 1 (.cons C1_1_0 1 0 (.cons C1_0_7 0 7 (.cons C1_0_6 0 6 (.cons C1_0_5 0 5 (.cons C1_0_4 0 4 (.cons C1_0_3 0 3 (.cons C1_0_2 0 2 (.cons C1_0_1 0 1 (.cons C1_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))
lemma C1_generated : multiply HyData ThetaxData=C1Data := by rfl
def C1n_7_0 : Expr := (.mul (.neg (.num 1)) C1_7_0)
def C1n_6_1 : Expr := (.mul (.neg (.num 1)) C1_6_1)
def C1n_6_0 : Expr := (.mul (.neg (.num 1)) C1_6_0)
def C1n_5_2 : Expr := (.mul (.neg (.num 1)) C1_5_2)
def C1n_5_1 : Expr := (.mul (.neg (.num 1)) C1_5_1)
def C1n_5_0 : Expr := (.mul (.neg (.num 1)) C1_5_0)
def C1n_4_3 : Expr := (.mul (.neg (.num 1)) C1_4_3)
def C1n_4_2 : Expr := (.mul (.neg (.num 1)) C1_4_2)
def C1n_4_1 : Expr := (.mul (.neg (.num 1)) C1_4_1)
def C1n_4_0 : Expr := (.mul (.neg (.num 1)) C1_4_0)
def C1n_3_4 : Expr := (.mul (.neg (.num 1)) C1_3_4)
def C1n_3_3 : Expr := (.mul (.neg (.num 1)) C1_3_3)
def C1n_3_2 : Expr := (.mul (.neg (.num 1)) C1_3_2)
def C1n_3_1 : Expr := (.mul (.neg (.num 1)) C1_3_1)
def C1n_3_0 : Expr := (.mul (.neg (.num 1)) C1_3_0)
def C1n_2_5 : Expr := (.mul (.neg (.num 1)) C1_2_5)
def C1n_2_4 : Expr := (.mul (.neg (.num 1)) C1_2_4)
def C1n_2_3 : Expr := (.mul (.neg (.num 1)) C1_2_3)
def C1n_2_2 : Expr := (.mul (.neg (.num 1)) C1_2_2)
def C1n_2_1 : Expr := (.mul (.neg (.num 1)) C1_2_1)
def C1n_2_0 : Expr := (.mul (.neg (.num 1)) C1_2_0)
def C1n_1_6 : Expr := (.mul (.neg (.num 1)) C1_1_6)
def C1n_1_5 : Expr := (.mul (.neg (.num 1)) C1_1_5)
def C1n_1_4 : Expr := (.mul (.neg (.num 1)) C1_1_4)
def C1n_1_3 : Expr := (.mul (.neg (.num 1)) C1_1_3)
def C1n_1_2 : Expr := (.mul (.neg (.num 1)) C1_1_2)
def C1n_1_1 : Expr := (.mul (.neg (.num 1)) C1_1_1)
def C1n_1_0 : Expr := (.mul (.neg (.num 1)) C1_1_0)
def C1n_0_7 : Expr := (.mul (.neg (.num 1)) C1_0_7)
def C1n_0_6 : Expr := (.mul (.neg (.num 1)) C1_0_6)
def C1n_0_5 : Expr := (.mul (.neg (.num 1)) C1_0_5)
def C1n_0_4 : Expr := (.mul (.neg (.num 1)) C1_0_4)
def C1n_0_3 : Expr := (.mul (.neg (.num 1)) C1_0_3)
def C1n_0_2 : Expr := (.mul (.neg (.num 1)) C1_0_2)
def C1n_0_1 : Expr := (.mul (.neg (.num 1)) C1_0_1)
def C1n_0_0 : Expr := (.mul (.neg (.num 1)) C1_0_0)
def C1nData : Biv := (.cons C1n_7_0 7 0 (.cons C1n_6_1 6 1 (.cons C1n_6_0 6 0 (.cons C1n_5_2 5 2 (.cons C1n_5_1 5 1 (.cons C1n_5_0 5 0 (.cons C1n_4_3 4 3 (.cons C1n_4_2 4 2 (.cons C1n_4_1 4 1 (.cons C1n_4_0 4 0 (.cons C1n_3_4 3 4 (.cons C1n_3_3 3 3 (.cons C1n_3_2 3 2 (.cons C1n_3_1 3 1 (.cons C1n_3_0 3 0 (.cons C1n_2_5 2 5 (.cons C1n_2_4 2 4 (.cons C1n_2_3 2 3 (.cons C1n_2_2 2 2 (.cons C1n_2_1 2 1 (.cons C1n_2_0 2 0 (.cons C1n_1_6 1 6 (.cons C1n_1_5 1 5 (.cons C1n_1_4 1 4 (.cons C1n_1_3 1 3 (.cons C1n_1_2 1 2 (.cons C1n_1_1 1 1 (.cons C1n_1_0 1 0 (.cons C1n_0_7 0 7 (.cons C1n_0_6 0 6 (.cons C1n_0_5 0 5 (.cons C1n_0_4 0 4 (.cons C1n_0_3 0 3 (.cons C1n_0_2 0 2 (.cons C1n_0_1 0 1 (.cons C1n_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))
lemma C1n_generated : scale (.neg (.num 1)) 0 0 C1Data=C1nData := by rfl
def C_7_0 : Expr := (.add C0_7_0 C1n_7_0)
def C_6_1 : Expr := (.add C0_6_1 C1n_6_1)
def C_6_0 : Expr := (.add C0_6_0 C1n_6_0)
def C_5_2 : Expr := (.add C0_5_2 C1n_5_2)
def C_5_1 : Expr := (.add C0_5_1 C1n_5_1)
def C_5_0 : Expr := (.add C0_5_0 C1n_5_0)
def C_4_3 : Expr := (.add C0_4_3 C1n_4_3)
def C_4_2 : Expr := (.add C0_4_2 C1n_4_2)
def C_4_1 : Expr := (.add C0_4_1 C1n_4_1)
def C_4_0 : Expr := (.add C0_4_0 C1n_4_0)
def C_3_4 : Expr := (.add C0_3_4 C1n_3_4)
def C_3_3 : Expr := (.add C0_3_3 C1n_3_3)
def C_3_2 : Expr := (.add C0_3_2 C1n_3_2)
def C_3_1 : Expr := (.add C0_3_1 C1n_3_1)
def C_3_0 : Expr := (.add C0_3_0 C1n_3_0)
def C_2_5 : Expr := (.add C0_2_5 C1n_2_5)
def C_2_4 : Expr := (.add C0_2_4 C1n_2_4)
def C_2_3 : Expr := (.add C0_2_3 C1n_2_3)
def C_2_2 : Expr := (.add C0_2_2 C1n_2_2)
def C_2_1 : Expr := (.add C0_2_1 C1n_2_1)
def C_2_0 : Expr := (.add C0_2_0 C1n_2_0)
def C_1_6 : Expr := (.add C0_1_6 C1n_1_6)
def C_1_5 : Expr := (.add C0_1_5 C1n_1_5)
def C_1_4 : Expr := (.add C0_1_4 C1n_1_4)
def C_1_3 : Expr := (.add C0_1_3 C1n_1_3)
def C_1_2 : Expr := (.add C0_1_2 C1n_1_2)
def C_1_1 : Expr := (.add C0_1_1 C1n_1_1)
def C_1_0 : Expr := (.add C0_1_0 C1n_1_0)
def C_0_7 : Expr := (.add C0_0_7 C1n_0_7)
def C_0_6 : Expr := (.add C0_0_6 C1n_0_6)
def C_0_5 : Expr := (.add C0_0_5 C1n_0_5)
def C_0_4 : Expr := (.add C0_0_4 C1n_0_4)
def C_0_3 : Expr := (.add C0_0_3 C1n_0_3)
def C_0_2 : Expr := (.add C0_0_2 C1n_0_2)
def C_0_1 : Expr := (.add C0_0_1 C1n_0_1)
def C_0_0 : Expr := (.add C0_0_0 C1n_0_0)
def CData : Biv := (.cons C_7_0 7 0 (.cons C_6_1 6 1 (.cons C_6_0 6 0 (.cons C_5_2 5 2 (.cons C_5_1 5 1 (.cons C_5_0 5 0 (.cons C_4_3 4 3 (.cons C_4_2 4 2 (.cons C_4_1 4 1 (.cons C_4_0 4 0 (.cons C_3_4 3 4 (.cons C_3_3 3 3 (.cons C_3_2 3 2 (.cons C_3_1 3 1 (.cons C_3_0 3 0 (.cons C_2_5 2 5 (.cons C_2_4 2 4 (.cons C_2_3 2 3 (.cons C_2_2 2 2 (.cons C_2_1 2 1 (.cons C_2_0 2 0 (.cons C_1_6 1 6 (.cons C_1_5 1 5 (.cons C_1_4 1 4 (.cons C_1_3 1 3 (.cons C_1_2 1 2 (.cons C_1_1 1 1 (.cons C_1_0 1 0 (.cons C_0_7 0 7 (.cons C_0_6 0 6 (.cons C_0_5 0 5 (.cons C_0_4 0 4 (.cons C_0_3 0 3 (.cons C_0_2 0 2 (.cons C_0_1 0 1 (.cons C_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))
lemma C_generated : merge 512 C0Data C1nData=CData := by rfl
def Right_10_0 : Expr := (.mul U_3_0 C_7_0)
def Right_9_1 : Expr := (.add (.mul U_3_0 C_6_1) (.mul U_2_1 C_7_0))
def Right_9_0 : Expr := (.add (.mul U_3_0 C_6_0) (.mul U_2_0 C_7_0))
def Right_8_2 : Expr := (.add (.mul U_3_0 C_5_2) (.mul U_2_1 C_6_1))
def Right_8_1 : Expr := (.add (.mul U_3_0 C_5_1) (.add (.mul U_2_1 C_6_0) (.mul U_2_0 C_6_1)))
def Right_8_0 : Expr := (.add (.mul U_3_0 C_5_0) (.mul U_2_0 C_6_0))
def Right_7_3 : Expr := (.add (.mul U_3_0 C_4_3) (.add (.mul U_2_1 C_5_2) (.mul U_0_3 C_7_0)))
def Right_7_2 : Expr := (.add (.mul U_3_0 C_4_2) (.add (.mul U_2_1 C_5_1) (.add (.mul U_2_0 C_5_2) (.mul U_0_2 C_7_0))))
def Right_7_1 : Expr := (.add (.mul U_3_0 C_4_1) (.add (.mul U_2_1 C_5_0) (.mul U_2_0 C_5_1)))
def Right_7_0 : Expr := (.add (.mul U_3_0 C_4_0) (.add (.mul U_2_0 C_5_0) (.mul U_0_0 C_7_0)))
def Right_6_4 : Expr := (.add (.mul U_3_0 C_3_4) (.add (.mul U_2_1 C_4_3) (.mul U_0_3 C_6_1)))
def Right_6_3 : Expr := (.add (.mul U_3_0 C_3_3) (.add (.mul U_2_1 C_4_2) (.add (.mul U_2_0 C_4_3) (.add (.mul U_0_3 C_6_0) (.mul U_0_2 C_6_1)))))
def Right_6_2 : Expr := (.add (.mul U_3_0 C_3_2) (.add (.mul U_2_1 C_4_1) (.add (.mul U_2_0 C_4_2) (.mul U_0_2 C_6_0))))
def Right_6_1 : Expr := (.add (.mul U_3_0 C_3_1) (.add (.mul U_2_1 C_4_0) (.add (.mul U_2_0 C_4_1) (.mul U_0_0 C_6_1))))
def Right_6_0 : Expr := (.add (.mul U_3_0 C_3_0) (.add (.mul U_2_0 C_4_0) (.mul U_0_0 C_6_0)))
def Right_5_5 : Expr := (.add (.mul U_3_0 C_2_5) (.add (.mul U_2_1 C_3_4) (.mul U_0_3 C_5_2)))
def Right_5_4 : Expr := (.add (.mul U_3_0 C_2_4) (.add (.mul U_2_1 C_3_3) (.add (.mul U_2_0 C_3_4) (.add (.mul U_0_3 C_5_1) (.mul U_0_2 C_5_2)))))
def Right_5_3 : Expr := (.add (.mul U_3_0 C_2_3) (.add (.mul U_2_1 C_3_2) (.add (.mul U_2_0 C_3_3) (.add (.mul U_0_3 C_5_0) (.mul U_0_2 C_5_1)))))
def Right_5_2 : Expr := (.add (.mul U_3_0 C_2_2) (.add (.mul U_2_1 C_3_1) (.add (.mul U_2_0 C_3_2) (.add (.mul U_0_2 C_5_0) (.mul U_0_0 C_5_2)))))
def Right_5_1 : Expr := (.add (.mul U_3_0 C_2_1) (.add (.mul U_2_1 C_3_0) (.add (.mul U_2_0 C_3_1) (.mul U_0_0 C_5_1))))
def Right_5_0 : Expr := (.add (.mul U_3_0 C_2_0) (.add (.mul U_2_0 C_3_0) (.mul U_0_0 C_5_0)))
def Right_4_6 : Expr := (.add (.mul U_3_0 C_1_6) (.add (.mul U_2_1 C_2_5) (.mul U_0_3 C_4_3)))
def Right_4_5 : Expr := (.add (.mul U_3_0 C_1_5) (.add (.mul U_2_1 C_2_4) (.add (.mul U_2_0 C_2_5) (.add (.mul U_0_3 C_4_2) (.mul U_0_2 C_4_3)))))
def Right_4_4 : Expr := (.add (.mul U_3_0 C_1_4) (.add (.mul U_2_1 C_2_3) (.add (.mul U_2_0 C_2_4) (.add (.mul U_0_3 C_4_1) (.mul U_0_2 C_4_2)))))
def Right_4_3 : Expr := (.add (.mul U_3_0 C_1_3) (.add (.mul U_2_1 C_2_2) (.add (.mul U_2_0 C_2_3) (.add (.mul U_0_3 C_4_0) (.add (.mul U_0_2 C_4_1) (.mul U_0_0 C_4_3))))))
def Right_4_2 : Expr := (.add (.mul U_3_0 C_1_2) (.add (.mul U_2_1 C_2_1) (.add (.mul U_2_0 C_2_2) (.add (.mul U_0_2 C_4_0) (.mul U_0_0 C_4_2)))))
def Right_4_1 : Expr := (.add (.mul U_3_0 C_1_1) (.add (.mul U_2_1 C_2_0) (.add (.mul U_2_0 C_2_1) (.mul U_0_0 C_4_1))))
def Right_4_0 : Expr := (.add (.mul U_3_0 C_1_0) (.add (.mul U_2_0 C_2_0) (.mul U_0_0 C_4_0)))
def Right_3_7 : Expr := (.add (.mul U_3_0 C_0_7) (.add (.mul U_2_1 C_1_6) (.mul U_0_3 C_3_4)))
def Right_3_6 : Expr := (.add (.mul U_3_0 C_0_6) (.add (.mul U_2_1 C_1_5) (.add (.mul U_2_0 C_1_6) (.add (.mul U_0_3 C_3_3) (.mul U_0_2 C_3_4)))))
def Right_3_5 : Expr := (.add (.mul U_3_0 C_0_5) (.add (.mul U_2_1 C_1_4) (.add (.mul U_2_0 C_1_5) (.add (.mul U_0_3 C_3_2) (.mul U_0_2 C_3_3)))))
def Right_3_4 : Expr := (.add (.mul U_3_0 C_0_4) (.add (.mul U_2_1 C_1_3) (.add (.mul U_2_0 C_1_4) (.add (.mul U_0_3 C_3_1) (.add (.mul U_0_2 C_3_2) (.mul U_0_0 C_3_4))))))
def Right_3_3 : Expr := (.add (.mul U_3_0 C_0_3) (.add (.mul U_2_1 C_1_2) (.add (.mul U_2_0 C_1_3) (.add (.mul U_0_3 C_3_0) (.add (.mul U_0_2 C_3_1) (.mul U_0_0 C_3_3))))))
def Right_3_2 : Expr := (.add (.mul U_3_0 C_0_2) (.add (.mul U_2_1 C_1_1) (.add (.mul U_2_0 C_1_2) (.add (.mul U_0_2 C_3_0) (.mul U_0_0 C_3_2)))))
def Right_3_1 : Expr := (.add (.mul U_3_0 C_0_1) (.add (.mul U_2_1 C_1_0) (.add (.mul U_2_0 C_1_1) (.mul U_0_0 C_3_1))))
def Right_3_0 : Expr := (.add (.mul U_3_0 C_0_0) (.add (.mul U_2_0 C_1_0) (.mul U_0_0 C_3_0)))
def Right_2_8 : Expr := (.add (.mul U_2_1 C_0_7) (.mul U_0_3 C_2_5))
def Right_2_7 : Expr := (.add (.mul U_2_1 C_0_6) (.add (.mul U_2_0 C_0_7) (.add (.mul U_0_3 C_2_4) (.mul U_0_2 C_2_5))))
def Right_2_6 : Expr := (.add (.mul U_2_1 C_0_5) (.add (.mul U_2_0 C_0_6) (.add (.mul U_0_3 C_2_3) (.mul U_0_2 C_2_4))))
def Right_2_5 : Expr := (.add (.mul U_2_1 C_0_4) (.add (.mul U_2_0 C_0_5) (.add (.mul U_0_3 C_2_2) (.add (.mul U_0_2 C_2_3) (.mul U_0_0 C_2_5)))))
def Right_2_4 : Expr := (.add (.mul U_2_1 C_0_3) (.add (.mul U_2_0 C_0_4) (.add (.mul U_0_3 C_2_1) (.add (.mul U_0_2 C_2_2) (.mul U_0_0 C_2_4)))))
def Right_2_3 : Expr := (.add (.mul U_2_1 C_0_2) (.add (.mul U_2_0 C_0_3) (.add (.mul U_0_3 C_2_0) (.add (.mul U_0_2 C_2_1) (.mul U_0_0 C_2_3)))))
def Right_2_2 : Expr := (.add (.mul U_2_1 C_0_1) (.add (.mul U_2_0 C_0_2) (.add (.mul U_0_2 C_2_0) (.mul U_0_0 C_2_2))))
def Right_2_1 : Expr := (.add (.mul U_2_1 C_0_0) (.add (.mul U_2_0 C_0_1) (.mul U_0_0 C_2_1)))
def Right_2_0 : Expr := (.add (.mul U_2_0 C_0_0) (.mul U_0_0 C_2_0))
def Right_1_9 : Expr := (.mul U_0_3 C_1_6)
def Right_1_8 : Expr := (.add (.mul U_0_3 C_1_5) (.mul U_0_2 C_1_6))
def Right_1_7 : Expr := (.add (.mul U_0_3 C_1_4) (.mul U_0_2 C_1_5))
def Right_1_6 : Expr := (.add (.mul U_0_3 C_1_3) (.add (.mul U_0_2 C_1_4) (.mul U_0_0 C_1_6)))
def Right_1_5 : Expr := (.add (.mul U_0_3 C_1_2) (.add (.mul U_0_2 C_1_3) (.mul U_0_0 C_1_5)))
def Right_1_4 : Expr := (.add (.mul U_0_3 C_1_1) (.add (.mul U_0_2 C_1_2) (.mul U_0_0 C_1_4)))
def Right_1_3 : Expr := (.add (.mul U_0_3 C_1_0) (.add (.mul U_0_2 C_1_1) (.mul U_0_0 C_1_3)))
def Right_1_2 : Expr := (.add (.mul U_0_2 C_1_0) (.mul U_0_0 C_1_2))
def Right_1_1 : Expr := (.mul U_0_0 C_1_1)
def Right_1_0 : Expr := (.mul U_0_0 C_1_0)
def Right_0_10 : Expr := (.mul U_0_3 C_0_7)
def Right_0_9 : Expr := (.add (.mul U_0_3 C_0_6) (.mul U_0_2 C_0_7))
def Right_0_8 : Expr := (.add (.mul U_0_3 C_0_5) (.mul U_0_2 C_0_6))
def Right_0_7 : Expr := (.add (.mul U_0_3 C_0_4) (.add (.mul U_0_2 C_0_5) (.mul U_0_0 C_0_7)))
def Right_0_6 : Expr := (.add (.mul U_0_3 C_0_3) (.add (.mul U_0_2 C_0_4) (.mul U_0_0 C_0_6)))
def Right_0_5 : Expr := (.add (.mul U_0_3 C_0_2) (.add (.mul U_0_2 C_0_3) (.mul U_0_0 C_0_5)))
def Right_0_4 : Expr := (.add (.mul U_0_3 C_0_1) (.add (.mul U_0_2 C_0_2) (.mul U_0_0 C_0_4)))
def Right_0_3 : Expr := (.add (.mul U_0_3 C_0_0) (.add (.mul U_0_2 C_0_1) (.mul U_0_0 C_0_3)))
def Right_0_2 : Expr := (.add (.mul U_0_2 C_0_0) (.mul U_0_0 C_0_2))
def Right_0_1 : Expr := (.mul U_0_0 C_0_1)
def Right_0_0 : Expr := (.mul U_0_0 C_0_0)
def RightData : Biv := (.cons Right_10_0 10 0 (.cons Right_9_1 9 1 (.cons Right_9_0 9 0 (.cons Right_8_2 8 2 (.cons Right_8_1 8 1 (.cons Right_8_0 8 0 (.cons Right_7_3 7 3 (.cons Right_7_2 7 2 (.cons Right_7_1 7 1 (.cons Right_7_0 7 0 (.cons Right_6_4 6 4 (.cons Right_6_3 6 3 (.cons Right_6_2 6 2 (.cons Right_6_1 6 1 (.cons Right_6_0 6 0 (.cons Right_5_5 5 5 (.cons Right_5_4 5 4 (.cons Right_5_3 5 3 (.cons Right_5_2 5 2 (.cons Right_5_1 5 1 (.cons Right_5_0 5 0 (.cons Right_4_6 4 6 (.cons Right_4_5 4 5 (.cons Right_4_4 4 4 (.cons Right_4_3 4 3 (.cons Right_4_2 4 2 (.cons Right_4_1 4 1 (.cons Right_4_0 4 0 (.cons Right_3_7 3 7 (.cons Right_3_6 3 6 (.cons Right_3_5 3 5 (.cons Right_3_4 3 4 (.cons Right_3_3 3 3 (.cons Right_3_2 3 2 (.cons Right_3_1 3 1 (.cons Right_3_0 3 0 (.cons Right_2_8 2 8 (.cons Right_2_7 2 7 (.cons Right_2_6 2 6 (.cons Right_2_5 2 5 (.cons Right_2_4 2 4 (.cons Right_2_3 2 3 (.cons Right_2_2 2 2 (.cons Right_2_1 2 1 (.cons Right_2_0 2 0 (.cons Right_1_9 1 9 (.cons Right_1_8 1 8 (.cons Right_1_7 1 7 (.cons Right_1_6 1 6 (.cons Right_1_5 1 5 (.cons Right_1_4 1 4 (.cons Right_1_3 1 3 (.cons Right_1_2 1 2 (.cons Right_1_1 1 1 (.cons Right_1_0 1 0 (.cons Right_0_10 0 10 (.cons Right_0_9 0 9 (.cons Right_0_8 0 8 (.cons Right_0_7 0 7 (.cons Right_0_6 0 6 (.cons Right_0_5 0 5 (.cons Right_0_4 0 4 (.cons Right_0_3 0 3 (.cons Right_0_2 0 2 (.cons Right_0_1 0 1 (.cons Right_0_0 0 0 .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
lemma Right_generated : multiply UData CData=RightData := by rfl
theorem coefficient_10_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_10_0=ringEval v Right_10_0 := by
  apply identity_of_encoding_context v Left_10_0 Right_10_0 (19,9,8) (2^28)
  all_goals decide +kernel
theorem coefficient_9_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_9_1=ringEval v Right_9_1 := by
  apply identity_of_encoding_context v Left_9_1 Right_9_1 (18,10,8) (2^28)
  all_goals decide +kernel
theorem coefficient_9_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_9_0=ringEval v Right_9_0 := by
  apply identity_of_encoding_context v Left_9_0 Right_9_0 (18,9,9) (2^28)
  all_goals decide +kernel
theorem coefficient_8_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_8_2=ringEval v Right_8_2 := by
  apply identity_of_encoding_context v Left_8_2 Right_8_2 (17,11,8) (2^28)
  all_goals decide +kernel
theorem coefficient_8_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_8_1=ringEval v Right_8_1 := by
  apply identity_of_encoding_context v Left_8_1 Right_8_1 (17,10,9) (2^28)
  all_goals decide +kernel
theorem coefficient_8_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_8_0=ringEval v Right_8_0 := by
  apply identity_of_encoding_context v Left_8_0 Right_8_0 (17,9,10) (2^28)
  all_goals decide +kernel
theorem coefficient_7_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_7_3=ringEval v Right_7_3 := by
  apply identity_of_encoding_context v Left_7_3 Right_7_3 (16,12,8) (2^28)
  all_goals decide +kernel
theorem coefficient_7_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_7_2=ringEval v Right_7_2 := by
  apply identity_of_encoding_context v Left_7_2 Right_7_2 (16,11,9) (2^28)
  all_goals decide +kernel
theorem coefficient_7_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_7_1=ringEval v Right_7_1 := by
  apply identity_of_encoding_context v Left_7_1 Right_7_1 (16,10,10) (2^28)
  all_goals decide +kernel
theorem coefficient_7_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_7_0=ringEval v Right_7_0 := by
  apply identity_of_encoding_context v Left_7_0 Right_7_0 (16,9,11) (2^28)
  all_goals decide +kernel
theorem coefficient_6_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_6_4=ringEval v Right_6_4 := by
  apply identity_of_encoding_context v Left_6_4 Right_6_4 (15,13,8) (2^28)
  all_goals decide +kernel
theorem coefficient_6_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_6_3=ringEval v Right_6_3 := by
  apply identity_of_encoding_context v Left_6_3 Right_6_3 (15,12,9) (2^28)
  all_goals decide +kernel
theorem coefficient_6_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_6_2=ringEval v Right_6_2 := by
  apply identity_of_encoding_context v Left_6_2 Right_6_2 (15,11,10) (2^28)
  all_goals decide +kernel
theorem coefficient_6_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_6_1=ringEval v Right_6_1 := by
  apply identity_of_encoding_context v Left_6_1 Right_6_1 (15,10,11) (2^28)
  all_goals decide +kernel
theorem coefficient_6_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_6_0=ringEval v Right_6_0 := by
  apply identity_of_encoding_context v Left_6_0 Right_6_0 (15,9,12) (2^28)
  all_goals decide +kernel
theorem coefficient_5_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_5=ringEval v Right_5_5 := by
  apply identity_of_encoding_context v Left_5_5 Right_5_5 (14,14,8) (2^28)
  all_goals decide +kernel
theorem coefficient_5_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_4=ringEval v Right_5_4 := by
  apply identity_of_encoding_context v Left_5_4 Right_5_4 (14,13,9) (2^28)
  all_goals decide +kernel
theorem coefficient_5_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_3=ringEval v Right_5_3 := by
  apply identity_of_encoding_context v Left_5_3 Right_5_3 (14,12,10) (2^28)
  all_goals decide +kernel
theorem coefficient_5_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_2=ringEval v Right_5_2 := by
  apply identity_of_encoding_context v Left_5_2 Right_5_2 (14,11,11) (2^28)
  all_goals decide +kernel
theorem coefficient_5_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_1=ringEval v Right_5_1 := by
  apply identity_of_encoding_context v Left_5_1 Right_5_1 (14,10,12) (2^28)
  all_goals decide +kernel
theorem coefficient_5_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_5_0=ringEval v Right_5_0 := by
  apply identity_of_encoding_context v Left_5_0 Right_5_0 (14,9,13) (2^28)
  all_goals decide +kernel
theorem coefficient_4_6 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_6=ringEval v Right_4_6 := by
  apply identity_of_encoding_context v Left_4_6 Right_4_6 (13,15,8) (2^28)
  all_goals decide +kernel
theorem coefficient_4_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_5=ringEval v Right_4_5 := by
  apply identity_of_encoding_context v Left_4_5 Right_4_5 (13,14,9) (2^28)
  all_goals decide +kernel
theorem coefficient_4_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_4=ringEval v Right_4_4 := by
  apply identity_of_encoding_context v Left_4_4 Right_4_4 (13,13,10) (2^28)
  all_goals decide +kernel
theorem coefficient_4_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_3=ringEval v Right_4_3 := by
  apply identity_of_encoding_context v Left_4_3 Right_4_3 (13,12,11) (2^28)
  all_goals decide +kernel
theorem coefficient_4_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_2=ringEval v Right_4_2 := by
  apply identity_of_encoding_context v Left_4_2 Right_4_2 (13,11,12) (2^28)
  all_goals decide +kernel
theorem coefficient_4_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_1=ringEval v Right_4_1 := by
  apply identity_of_encoding_context v Left_4_1 Right_4_1 (13,10,13) (2^28)
  all_goals decide +kernel
theorem coefficient_4_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_4_0=ringEval v Right_4_0 := by
  apply identity_of_encoding_context v Left_4_0 Right_4_0 (13,9,14) (2^28)
  all_goals decide +kernel
theorem coefficient_3_7 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_7=ringEval v Right_3_7 := by
  apply identity_of_encoding_context v Left_3_7 Right_3_7 (12,16,8) (2^28)
  all_goals decide +kernel
theorem coefficient_3_6 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_6=ringEval v Right_3_6 := by
  apply identity_of_encoding_context v Left_3_6 Right_3_6 (12,15,9) (2^28)
  all_goals decide +kernel
theorem coefficient_3_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_5=ringEval v Right_3_5 := by
  apply identity_of_encoding_context v Left_3_5 Right_3_5 (12,14,10) (2^28)
  all_goals decide +kernel
theorem coefficient_3_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_4=ringEval v Right_3_4 := by
  apply identity_of_encoding_context v Left_3_4 Right_3_4 (12,13,11) (2^28)
  all_goals decide +kernel
theorem coefficient_3_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_3=ringEval v Right_3_3 := by
  apply identity_of_encoding_context v Left_3_3 Right_3_3 (12,12,12) (2^28)
  all_goals decide +kernel
theorem coefficient_3_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_2=ringEval v Right_3_2 := by
  apply identity_of_encoding_context v Left_3_2 Right_3_2 (12,11,13) (2^28)
  all_goals decide +kernel
theorem coefficient_3_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_1=ringEval v Right_3_1 := by
  apply identity_of_encoding_context v Left_3_1 Right_3_1 (12,10,14) (2^28)
  all_goals decide +kernel
theorem coefficient_3_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_3_0=ringEval v Right_3_0 := by
  apply identity_of_encoding_context v Left_3_0 Right_3_0 (12,9,15) (2^28)
  all_goals decide +kernel
theorem coefficient_2_8 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_8=ringEval v Right_2_8 := by
  apply identity_of_encoding_context v Left_2_8 Right_2_8 (11,17,8) (2^28)
  all_goals decide +kernel
theorem coefficient_2_7 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_7=ringEval v Right_2_7 := by
  apply identity_of_encoding_context v Left_2_7 Right_2_7 (11,16,9) (2^28)
  all_goals decide +kernel
theorem coefficient_2_6 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_6=ringEval v Right_2_6 := by
  apply identity_of_encoding_context v Left_2_6 Right_2_6 (11,15,10) (2^28)
  all_goals decide +kernel
theorem coefficient_2_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_5=ringEval v Right_2_5 := by
  apply identity_of_encoding_context v Left_2_5 Right_2_5 (11,14,11) (2^28)
  all_goals decide +kernel
theorem coefficient_2_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_4=ringEval v Right_2_4 := by
  apply identity_of_encoding_context v Left_2_4 Right_2_4 (11,13,12) (2^28)
  all_goals decide +kernel
theorem coefficient_2_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_3=ringEval v Right_2_3 := by
  apply identity_of_encoding_context v Left_2_3 Right_2_3 (11,12,13) (2^28)
  all_goals decide +kernel
theorem coefficient_2_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_2=ringEval v Right_2_2 := by
  apply identity_of_encoding_context v Left_2_2 Right_2_2 (11,11,14) (2^28)
  all_goals decide +kernel
theorem coefficient_2_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_1=ringEval v Right_2_1 := by
  apply identity_of_encoding_context v Left_2_1 Right_2_1 (11,10,15) (2^28)
  all_goals decide +kernel
theorem coefficient_2_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_2_0=ringEval v Right_2_0 := by
  apply identity_of_encoding_context v Left_2_0 Right_2_0 (11,9,16) (2^28)
  all_goals decide +kernel
theorem coefficient_1_9 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_9=ringEval v Right_1_9 := by
  apply identity_of_encoding_context v Left_1_9 Right_1_9 (10,18,8) (2^28)
  all_goals decide +kernel
theorem coefficient_1_8 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_8=ringEval v Right_1_8 := by
  apply identity_of_encoding_context v Left_1_8 Right_1_8 (10,17,9) (2^28)
  all_goals decide +kernel
theorem coefficient_1_7 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_7=ringEval v Right_1_7 := by
  apply identity_of_encoding_context v Left_1_7 Right_1_7 (10,16,10) (2^28)
  all_goals decide +kernel
theorem coefficient_1_6 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_6=ringEval v Right_1_6 := by
  apply identity_of_encoding_context v Left_1_6 Right_1_6 (10,15,11) (2^28)
  all_goals decide +kernel
theorem coefficient_1_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_5=ringEval v Right_1_5 := by
  apply identity_of_encoding_context v Left_1_5 Right_1_5 (10,14,12) (2^28)
  all_goals decide +kernel
theorem coefficient_1_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_4=ringEval v Right_1_4 := by
  apply identity_of_encoding_context v Left_1_4 Right_1_4 (10,13,13) (2^28)
  all_goals decide +kernel
theorem coefficient_1_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_3=ringEval v Right_1_3 := by
  apply identity_of_encoding_context v Left_1_3 Right_1_3 (10,12,14) (2^28)
  all_goals decide +kernel
theorem coefficient_1_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_2=ringEval v Right_1_2 := by
  apply identity_of_encoding_context v Left_1_2 Right_1_2 (10,11,15) (2^28)
  all_goals decide +kernel
theorem coefficient_1_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_1=ringEval v Right_1_1 := by
  apply identity_of_encoding_context v Left_1_1 Right_1_1 (10,10,16) (2^28)
  all_goals decide +kernel
theorem coefficient_1_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_1_0=ringEval v Right_1_0 := by
  apply identity_of_encoding_context v Left_1_0 Right_1_0 (10,9,17) (2^28)
  all_goals decide +kernel
theorem coefficient_0_10 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_10=ringEval v Right_0_10 := by
  apply identity_of_encoding_context v Left_0_10 Right_0_10 (9,19,8) (2^28)
  all_goals decide +kernel
theorem coefficient_0_9 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_9=ringEval v Right_0_9 := by
  apply identity_of_encoding_context v Left_0_9 Right_0_9 (9,18,9) (2^28)
  all_goals decide +kernel
theorem coefficient_0_8 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_8=ringEval v Right_0_8 := by
  apply identity_of_encoding_context v Left_0_8 Right_0_8 (9,17,10) (2^28)
  all_goals decide +kernel
theorem coefficient_0_7 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_7=ringEval v Right_0_7 := by
  apply identity_of_encoding_context v Left_0_7 Right_0_7 (9,16,11) (2^28)
  all_goals decide +kernel
theorem coefficient_0_6 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_6=ringEval v Right_0_6 := by
  apply identity_of_encoding_context v Left_0_6 Right_0_6 (9,15,12) (2^28)
  all_goals decide +kernel
theorem coefficient_0_5 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_5=ringEval v Right_0_5 := by
  apply identity_of_encoding_context v Left_0_5 Right_0_5 (9,14,13) (2^28)
  all_goals decide +kernel
theorem coefficient_0_4 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_4=ringEval v Right_0_4 := by
  apply identity_of_encoding_context v Left_0_4 Right_0_4 (9,13,14) (2^28)
  all_goals decide +kernel
theorem coefficient_0_3 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_3=ringEval v Right_0_3 := by
  apply identity_of_encoding_context v Left_0_3 Right_0_3 (9,12,15) (2^28)
  all_goals decide +kernel
theorem coefficient_0_2 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_2=ringEval v Right_0_2 := by
  apply identity_of_encoding_context v Left_0_2 Right_0_2 (9,11,16) (2^28)
  all_goals decide +kernel
theorem coefficient_0_1 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_1=ringEval v Right_0_1 := by
  apply identity_of_encoding_context v Left_0_1 Right_0_1 (9,10,17) (2^28)
  all_goals decide +kernel
theorem coefficient_0_0 {L : Type*} [CommRing L] (v : ℕ → L) :
    ringEval v Left_0_0=ringEval v Right_0_0 := by
  apply identity_of_encoding_context v Left_0_0 Right_0_0 (9,9,18) (2^28)
  all_goals decide +kernel
theorem data_identity {L : Type*} [CommRing L] (v : ℕ → L) (xx yy : L) :
    denote v xx yy LeftData=denote v xx yy RightData := by
  simp only [LeftData,RightData,denote,coefficient_10_0,coefficient_9_1,coefficient_9_0,coefficient_8_2,coefficient_8_1,coefficient_8_0,coefficient_7_3,coefficient_7_2,coefficient_7_1,coefficient_7_0,coefficient_6_4,coefficient_6_3,coefficient_6_2,coefficient_6_1,coefficient_6_0,coefficient_5_5,coefficient_5_4,coefficient_5_3,coefficient_5_2,coefficient_5_1,coefficient_5_0,coefficient_4_6,coefficient_4_5,coefficient_4_4,coefficient_4_3,coefficient_4_2,coefficient_4_1,coefficient_4_0,coefficient_3_7,coefficient_3_6,coefficient_3_5,coefficient_3_4,coefficient_3_3,coefficient_3_2,coefficient_3_1,coefficient_3_0,coefficient_2_8,coefficient_2_7,coefficient_2_6,coefficient_2_5,coefficient_2_4,coefficient_2_3,coefficient_2_2,coefficient_2_1,coefficient_2_0,coefficient_1_9,coefficient_1_8,coefficient_1_7,coefficient_1_6,coefficient_1_5,coefficient_1_4,coefficient_1_3,coefficient_1_2,coefficient_1_1,coefficient_1_0,coefficient_0_10,coefficient_0_9,coefficient_0_8,coefficient_0_7,coefficient_0_6,coefficient_0_5,coefficient_0_4,coefficient_0_3,coefficient_0_2,coefficient_0_1,coefficient_0_0]
theorem semantic_identity {L : Type*} [CommRing L] (v : ℕ → L) (xx yy : L) :
    let u := denote v xx yy UData
    let h := denote v xx yy HData
    let q := denote v xx yy ThetaData
    let j := denote v xx yy JData
    let ux := denote v xx yy UxData
    let uy := denote v xx yy UyData
    let hx := denote v xx yy HxData
    let hy := denote v xx yy HyData
    let qx := denote v xx yy ThetaxData
    let qy := denote v xx yy ThetayData
    h*(ux*qy-uy*qx)-2*q*(ux*hy-uy*hx)+3*j=u*(hx*qy-hy*qx) := by
  dsimp only
  have h := data_identity v xx yy
  simp only [← Right_generated,← C_generated,← C1n_generated,← C1_generated,← C0_generated,← Left_generated,← Left0_generated,← J3_generated,← QBneg_generated,← QB_generated,← B_generated,← B1n_generated,← B1_generated,← B0_generated,← HA_generated,← A_generated,← A1n_generated,← A1_generated,← A0_generated,multiply_denote,scale_denote,merge_denote,ringEval,Int.cast_ofNat] at h
  linear_combination h

def baseCoefficients (a b c d e f : K) : ℕ → K :=
  fun i => (context a b c d e f 0 0 1).get i
lemma H_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y HData=
      Hpoly a b c d e f := by
  change denote (fun i => (context (C a) (C b) (C c) (C d) (C e) (C f) x y 1).get i)
    x y HData=Hpoly a b c d e f
  exact H_evaluation (C a) (C b) (C c) (C d) (C e) (C f) x y
lemma Theta_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y ThetaData=
      Thetapoly a b c d e f := by
  change denote (fun i => (context (C a) (C b) (C c) (C d) (C e) (C f) x y 1).get i)
    x y ThetaData=Thetapoly a b c d e f
  exact Theta_evaluation (C a) (C b) (C c) (C d) (C e) (C f) x y
lemma J_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y JData=
      Jpoly a b c d e f := by
  change denote (fun i => (context (C a) (C b) (C c) (C d) (C e) (C f) x y 1).get i)
    x y JData=Jpoly a b c d e f
  exact J_evaluation (C a) (C b) (C c) (C d) (C e) (C f) x y
lemma U_binding (a b c d e f : K) :
    denote (fun i => C (baseCoefficients a b c d e f i)) x y UData=
      Upoly a b c d e f := by
  change denote (fun i => (context (C a) (C b) (C c) (C d) (C e) (C f) x y 1).get i)
    x y UData=Upoly a b c d e f
  rw [U_evaluation]
  simp only [TransitiveCubic.cubic,Upoly,one_pow,mul_one]
end DifferentialData

lemma relative_identity (a b c d e f : K) :
    let u := Upoly a b c d e f
    let h := Hpoly a b c d e f
    let q := Thetapoly a b c d e f
    let j := Jpoly a b c d e f
    h*(pderiv 0 u*pderiv 1 q-pderiv 1 u*pderiv 0 q)-
      2*q*(pderiv 0 u*pderiv 1 h-pderiv 1 u*pderiv 0 h)+3*j=
      u*(pderiv 0 h*pderiv 1 q-pderiv 1 h*pderiv 0 q) := by
  dsimp only
  let v := DifferentialData.baseCoefficients a b c d e f
  have h := DifferentialData.semantic_identity (fun i => C (v i)) x y
  dsimp only at h
  have hux : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.UxData=pderiv 0 (Upoly a b c d e f) := by
    rw [← DifferentialData.Ux_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dx]
    change pderiv 0 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.UData)=_
    rw [DifferentialData.U_binding]
  have huy : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.UyData=pderiv 1 (Upoly a b c d e f) := by
    rw [← DifferentialData.Uy_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dy]
    change pderiv 1 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.UData)=_
    rw [DifferentialData.U_binding]
  have hhx : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.HxData=pderiv 0 (Hpoly a b c d e f) := by
    rw [← DifferentialData.Hx_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dx]
    change pderiv 0 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.HData)=_
    rw [DifferentialData.H_binding]
  have hhy : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.HyData=pderiv 1 (Hpoly a b c d e f) := by
    rw [← DifferentialData.Hy_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dy]
    change pderiv 1 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.HData)=_
    rw [DifferentialData.H_binding]
  have hqx : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.ThetaxData=pderiv 0 (Thetapoly a b c d e f) := by
    rw [← DifferentialData.Thetax_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dx]
    change pderiv 0 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.ThetaData)=_
    rw [DifferentialData.Theta_binding]
  have hqy : PolynomialEncoding.BivariateExpressions.denote (fun i => C (v i)) x y
      DifferentialData.ThetayData=pderiv 1 (Thetapoly a b c d e f) := by
    rw [← DifferentialData.Thetay_generated,
      ← PolynomialEncoding.BivariateExpressions.pderiv_denote_dy]
    change pderiv 1 (PolynomialEncoding.BivariateExpressions.denote
      (fun i => C (DifferentialData.baseCoefficients a b c d e f i)) x y
      TransitiveCovariants.IdentityData.ThetaData)=_
    rw [DifferentialData.Theta_binding]
  simp only [hux,huy,hhx,hhy,hqx,hqy] at h
  simpa only [v,DifferentialData.U_binding,DifferentialData.H_binding,
    DifferentialData.Theta_binding,DifferentialData.J_binding] using h
#print axioms relative_identity
end TransitiveCovariants
