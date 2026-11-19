import Proposal.JacobianResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing

/-! Legal polynomial clearing on the auxiliary Jacobian hypersurface.
This theorem applies to every polynomial source. It does not assert ordinary
homogeneity, and it does not replace the fixed physical sextic by this model.
Transport to that sextic remains a separate obligation. The clearing machinery
is the shared construction credited to fqlx and collaborators.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/
noncomputable section
namespace CycleJacobianClearing
open HoldoutConstruction CycleJacobianEmbedding CycleJacobianHypersurface CycleJacobianResidue
open scoped BigOperators
local instance : Algebra ℤ TargetField := Ring.toIntAlgebra _
lemma hypersurface_irreducible : Irreducible hypersurface := by
  rw [← MulEquiv.irreducible_iff (f := MvPolynomial.finSuccEquiv ℂ 5),hypersurface_univariate]
  exact CycleJacobianDomain.equation_irreducible

/-- A legal cleared defect for every polynomial source on the auxiliary model. -/
theorem polynomial_clearing (A : Ambient) :
    ∃ D N₀ : Ambient, ∃ N : Fin 5 → Ambient, ∃ Q : Ambient,
      D≠0 ∧ IsRelPrime hypersurface D ∧
      (N₀*integerPartial 0 hypersurface+∑ i,N i*integerPartial i.succ hypersurface=A*D) ∧
      (residueDivNum (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ) D N₀ N=hypersurface*Q) ∧
      A*D^2-D*(N₀*integerPartial 0 hypersurface+∑ i,N i*integerPartial i.succ hypersurface)+
        hypersurface*residueDivNum (integerPartial 0) (fun i : Fin 5 => integerPartial i.succ) D N₀ N=
          hypersurface^2*Q := by
  obtain ⟨w,hw⟩ := target_residue_solution A
  apply residue_solution_clearing residueMap (integerPartial 0)
    (fun i : Fin 5 => integerPartial i.succ) tangent hypersurface A w
    hypersurface_irreducible residueMap_kernel normal_ne_zero
    (fun i => integerPartial_commute i.succ 0 hypersurface) tangent_apply
    (residue_common_representatives projection projection_surjective w)
  have hd : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 hypersurface)) w=
      ∑ i,(tangent i (w i)-w i*tangent i (residueMap (MvPolynomial.pderiv 0 hypersurface))/
        residueMap (MvPolynomial.pderiv 0 hypersurface)) := by
    simp only [residueDivergence,fieldDivergence,Finset.sum_sub_distrib,Finset.sum_div]
  rw [hd] at hw
  change (residueMap (MvPolynomial.pderiv 0 A)*residueMap (MvPolynomial.pderiv 0 hypersurface)-
    residueMap A*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface)))/
      (residueMap (MvPolynomial.pderiv 0 hypersurface))^2+
    ∑ i,(tangent i (w i)-w i*tangent i (residueMap (MvPolynomial.pderiv 0 hypersurface))/
      residueMap (MvPolynomial.pderiv 0 hypersurface))=0
  rw [hw]
  have hn : residueMap (MvPolynomial.pderiv 0 hypersurface)≠0 := normal_ne_zero
  field_simp
  ring
#print axioms polynomial_clearing
end CycleJacobianClearing
