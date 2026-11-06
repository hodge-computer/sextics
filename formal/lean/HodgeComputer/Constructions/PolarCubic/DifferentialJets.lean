import HodgeComputer.Constructions.PolarCubic.DifferentialData
namespace PolarCovariants.DifferentialData
open Lean.Grind.CommRing TransitiveSignedExpressions TransitiveBivariateExpressions
open PolarCovariants.IdentityData PolarCubicEncodingCheck ResidueFirstJets TrivSqZeroExt
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option maxHeartbeats 32000000
variable {K : Type*} [CommRing K]

private theorem jet_fst_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : TrivSqZeroExt K K).fst=(ofNat(n) : K) := rfl
private theorem jet_snd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : TrivSqZeroExt K K).snd=0 := rfl

theorem semantic_identityJet (v : ℕ → K) (x y k : K) (hkSquare : k^2=0) :
    let u := denote v x y UData+k*denote v x y UkData
    let h := denote v x y HData+k*denote v x y HkData
    let q := denote v x y ThetaData+k*denote v x y ThetakData
    let j := denote v x y JData+k*denote v x y JkData
    let ux := denote v x y UxData+k*denote v x y UkxData
    let uy := denote v x y UyData+k*denote v x y UkyData
    let hx := denote v x y HxData+k*denote v x y HkxData
    let hy := denote v x y HyData+k*denote v x y HkyData
    let qx := denote v x y ThetaxData+k*denote v x y ThetakxData
    let qy := denote v x y ThetayData+k*denote v x y ThetakyData
    ((3*j)+(h*qy*ux)+((-1)*h*qx*uy)+((-2)*hy*q*ux)+(2*hx*q*uy))=((hx*qy*u)+((-1)*hy*qx*u)) := by
  dsimp only
  have hbase := semantic_identity0 v x y
  have hfirst := semantic_identity1 v x y
  dsimp only at hbase hfirst
  generalize denote v x y UData=u0 at hbase hfirst ⊢
  generalize denote v x y HData=h0 at hbase hfirst ⊢
  generalize denote v x y ThetaData=q0 at hbase hfirst ⊢
  generalize denote v x y JData=j0 at hbase hfirst ⊢
  generalize denote v x y UxData=ux0 at hbase hfirst ⊢
  generalize denote v x y UyData=uy0 at hbase hfirst ⊢
  generalize denote v x y HxData=hx0 at hbase hfirst ⊢
  generalize denote v x y HyData=hy0 at hbase hfirst ⊢
  generalize denote v x y ThetaxData=qx0 at hbase hfirst ⊢
  generalize denote v x y ThetayData=qy0 at hbase hfirst ⊢
  generalize denote v x y UkData=u1 at hbase hfirst ⊢
  generalize denote v x y HkData=h1 at hbase hfirst ⊢
  generalize denote v x y ThetakData=q1 at hbase hfirst ⊢
  generalize denote v x y JkData=j1 at hbase hfirst ⊢
  generalize denote v x y UkxData=ux1 at hbase hfirst ⊢
  generalize denote v x y UkyData=uy1 at hbase hfirst ⊢
  generalize denote v x y HkxData=hx1 at hbase hfirst ⊢
  generalize denote v x y HkyData=hy1 at hbase hfirst ⊢
  generalize denote v x y ThetakxData=qx1 at hbase hfirst ⊢
  generalize denote v x y ThetakyData=qy1 at hbase hfirst ⊢
  let u : TrivSqZeroExt K K := (u0,u1)
  let h : TrivSqZeroExt K K := (h0,h1)
  let q : TrivSqZeroExt K K := (q0,q1)
  let j : TrivSqZeroExt K K := (j0,j1)
  let ux : TrivSqZeroExt K K := (ux0,ux1)
  let uy : TrivSqZeroExt K K := (uy0,uy1)
  let hx : TrivSqZeroExt K K := (hx0,hx1)
  let hy : TrivSqZeroExt K K := (hy0,hy1)
  let qx : TrivSqZeroExt K K := (qx0,qx1)
  let qy : TrivSqZeroExt K K := (qy0,qy1)
  have hh : (((3*j)+(h*qy*ux)+((-1)*h*qx*uy)+((-2)*hy*q*ux)+(2*hx*q*uy)) :
      TrivSqZeroExt K K)=((hx*qy*u)+((-1)*hy*qx*u)) := by
    apply TrivSqZeroExt.ext
    · simpa only [fst_mul,fst_add,fst_sub,fst_neg,fst_natCast,fst_intCast,
        jet_fst_ofNat,fst_zero,fst_one,fst_mk,u,h,q,j,ux,uy,hx,hy,qx,qy]
        using hbase
    · have hh1 := hfirst
      simp only [snd_mul,snd_add,snd_sub,snd_neg,snd_natCast,snd_intCast,
        fst_mul,fst_add,fst_sub,fst_neg,fst_natCast,fst_intCast,
        jet_fst_ofNat,jet_snd_ofNat,fst_zero,fst_one,snd_zero,snd_one,fst_mk,snd_mk,
        smul_eq_mul,op_smul_eq_smul,u,h,q,j,ux,uy,hx,hy,qx,qy]
      norm_num
      linear_combination hh1
  have result := congrArg (squareZeroEval k hkSquare) hh
  simpa only [map_add,map_sub,map_neg,map_mul,map_ofNat,map_zero,map_one,
    squareZeroEval_mk,u,h,q,j,ux,uy,hx,hy,qx,qy] using result
end PolarCovariants.DifferentialData
#print axioms PolarCovariants.DifferentialData.semantic_identityJet
