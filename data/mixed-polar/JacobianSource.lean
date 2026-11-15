import Proposal.JacobianResidue

/-! The polynomial numerator obtained from the balanced xyz variation of
the exact mixed-polar cubic. The polynomial-family residue theorem applies
to this source without imposing a denominator bound. Prepared with Codex
assistance, using the shared constructions credited in JacobianResidue. -/
noncomputable section
namespace MixedPolarJacobianSource
open HoldoutConstruction MixedPolarJacobianHypersurface
  MixedPolarJacobianEmbedding MixedPolarJacobianResidue
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)

/-- Ambient coordinate order is Y,T,c1,c2,R,X. -/
def sourceNumerator : Ambient :=
  v 2*v 3*(v 4+v 3^6*v 1)*
    ((108*(v 4+v 1)*(v 4+v 2^6*v 1)-2*v 2^4*v 4*v 1)*v 5+
      3*v 2^3*v 3^2*v 4^2*(v 4+v 1)*v 1)
def source : Ambient := MvPolynomial.C (1/3456 : ℂ)*sourceNumerator

lemma source_normal : MvPolynomial.pderiv 0 source=0 := by
  have h2 : MvPolynomial.pderiv 0 (2 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 2
  have h3 : MvPolynomial.pderiv 0 (3 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 3
  have h108 : MvPolynomial.pderiv 0 (108 : Ambient)=0 := (MvPolynomial.pderiv 0).map_natCast 108
  norm_num [source,sourceNumerator,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X,Pi.single_apply,Fin.ext_iff,h2,h3,h108]

theorem source_residue_solution :
    ∃ w : Fin 5 → TargetField,
      residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 hypersurface)) w=
        -(residueMap (MvPolynomial.pderiv 0 source)/residueMap (MvPolynomial.pderiv 0 hypersurface)-
          residueMap source*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface))/
            (residueMap (MvPolynomial.pderiv 0 hypersurface))^2) :=
  target_residue_solution source

end MixedPolarJacobianSource
#print axioms MixedPolarJacobianSource.source_residue_solution
