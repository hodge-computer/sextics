import HodgeComputer.Constructions.TransitiveCubic.IdentityData
namespace TransitiveCovariants.IdentityData
open PolynomialEncoding.BivariateExpressions TransitiveCovariants.Reflection
set_option maxRecDepth 131072
lemma Hp2_generated : multiply HData HData=Hp2Data := by rfl
lemma Hp3_generated : multiply HData Hp2Data=Hp3Data := by rfl
lemma Hp4_generated : multiply HData Hp3Data=Hp4Data := by rfl
lemma Hp5_generated : multiply HData Hp4Data=Hp5Data := by rfl
lemma Hp6_generated : multiply HData Hp5Data=Hp6Data := by rfl
lemma Up2_generated : multiply UData UData=Up2Data := by rfl
lemma Up3_generated : multiply UData Up2Data=Up3Data := by rfl
lemma Up4_generated : multiply UData Up3Data=Up4Data := by rfl
lemma Up5_generated : multiply UData Up4Data=Up5Data := by rfl
lemma Qp2_generated : multiply ThetaData ThetaData=Qp2Data := by rfl
lemma Qp3_generated : multiply ThetaData Qp2Data=Qp3Data := by rfl
lemma Leftp0_generated : multiply JData JData=Leftp0Data := by rfl
lemma Left_generated : scale (.num 27) 0 0 Leftp0Data=LeftData := by rfl
lemma T0c_generated : scale (.num 108) 0 0 Qp3Data=T0cData := by rfl
lemma T1p0_generated : multiply ThetaData Hp4Data=T1p0Data := by rfl
lemma T1c_generated : scale (.mul (.num 36) SExpr) 0 0 T1p0Data=T1cData := by rfl
lemma T2c_generated : scale (.neg TExpr) 0 0 Hp6Data=T2cData := by rfl
lemma T3p0_generated : multiply Up2Data Qp2Data=T3p0Data := by rfl
lemma T3c_generated : scale (.mul (.num 243) TExpr) 0 0 T3p0Data=T3cData := by rfl
lemma T4p0_generated : multiply ThetaData Up4Data=T4p0Data := by rfl
lemma T4c_generated : scale (.mul (.neg (.num 8748)) (.pow SExpr 3)) 0 0 T4p0Data=T4cData := by rfl
lemma T5p0_generated : multiply ThetaData Up3Data=T5p0Data := by rfl
lemma T5p1_generated : multiply T5p0Data HData=T5p1Data := by rfl
lemma T5c_generated : scale (.mul (.num 486) (.mul SExpr TExpr)) 0 0 T5p1Data=T5cData := by rfl
lemma T6p0_generated : multiply ThetaData Up2Data=T6p0Data := by rfl
lemma T6p1_generated : multiply T6p0Data Hp2Data=T6p1Data := by rfl
lemma T6c_generated : scale (.mul (.neg (.num 1944)) (.pow SExpr 2)) 0 0 T6p1Data=T6cData := by rfl
lemma T7p0_generated : multiply ThetaData UData=T7p0Data := by rfl
lemma T7p1_generated : multiply T7p0Data Hp3Data=T7p1Data := by rfl
lemma T7c_generated : scale (.mul (.neg (.num 54)) TExpr) 0 0 T7p1Data=T7cData := by rfl
lemma T8p0_generated : multiply Up5Data HData=T8p0Data := by rfl
lemma T8c_generated : scale (.mul (.neg (.num 34992)) (.pow SExpr 4)) 0 0 T8p0Data=T8cData := by rfl
lemma T9p0_generated : multiply Up4Data Hp2Data=T9p0Data := by rfl
lemma T9c_generated : scale (.mul (.neg (.num 2673)) (.mul (.pow SExpr 2) TExpr)) 0 0 T9p0Data=T9cData := by rfl
lemma T10p0_generated : multiply Up3Data Hp3Data=T10p0Data := by rfl
lemma T10c_generated : scale (.mul (.neg (.num 108)) (.pow TExpr 2)) 0 0 T10p0Data=T10cData := by rfl
lemma T11p0_generated : multiply Up2Data Hp4Data=T11p0Data := by rfl
lemma T11c_generated : scale (.mul (.num 162) (.mul SExpr TExpr)) 0 0 T11p0Data=T11cData := by rfl
lemma T12p0_generated : multiply UData Hp5Data=T12p0Data := by rfl
lemma T12c_generated : scale (.mul (.neg (.num 144)) (.pow SExpr 2)) 0 0 T12p0Data=T12cData := by rfl
lemma R11_generated : merge 512 T11cData T12cData=R11Data := by rfl
lemma R10_generated : merge 512 T10cData R11Data=R10Data := by rfl
lemma R9_generated : merge 512 T9cData R10Data=R9Data := by rfl
lemma R8_generated : merge 512 T8cData R9Data=R8Data := by rfl
lemma R7_generated : merge 512 T7cData R8Data=R7Data := by rfl
lemma R6_generated : merge 512 T6cData R7Data=R6Data := by rfl
lemma R5_generated : merge 512 T5cData R6Data=R5Data := by rfl
lemma R4_generated : merge 512 T4cData R5Data=R4Data := by rfl
lemma R3_generated : merge 512 T3cData R4Data=R3Data := by rfl
lemma R2_generated : merge 512 T2cData R3Data=R2Data := by rfl
lemma R1_generated : merge 512 T1cData R2Data=R1Data := by rfl
lemma Right_generated : merge 512 T0cData R1Data=RightData := by rfl
end TransitiveCovariants.IdentityData
