import Proposal.PhysicalField
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback

/-! The final reduction on the exact mixed-polar field. A solution of its
specified residue-divergence equation suffices for the protected certificate;
the legal clearing and homogenization are supplied by the shared constructions
of fqlx and project collaborators. The final primitive module supplies its residue-solution hypothesis.
Original cycle-three work prepared with OpenAI Codex assistance for hodgepodgeconjecture.
Adapted to mixed-polar for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CyclePhysical
open HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

theorem certificate_of_residue_solution
    (w : Fin 5 → FunctionField)
    (hw : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) w =
      -(residueMap (MvPolynomial.pderiv 0 source)/residueMap (MvPolynomial.pderiv 0 sextic)-
        residueMap source*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 sextic))/
          (residueMap (MvPolynomial.pderiv 0 sextic))^2)) :
    HodgeComputer.HasCertificate sextic source 1 := by
  have hd : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) w =
      ∑ i,(tangent i (w i)-w i*tangent i (residueMap (MvPolynomial.pderiv 0 sextic))/
        residueMap (MvPolynomial.pderiv 0 sextic)) := by
    simp only [residueDivergence,fieldDivergence,Finset.sum_sub_distrib,Finset.sum_div]
  obtain ⟨D,N₀,N,Q,hD,hlegal,hnormal,hdiv,_⟩ :=
    residue_solution_clearing residueMap (integerPartial 0)
      (fun i : Fin 5 => integerPartial i.succ) tangent sextic source w
      sextic_irreducible residueMap_kernel normal_ne_zero
      (fun i => integerPartial_commute i.succ 0 sextic) tangent_apply
      (residue_common_representatives projection projection_surjective w) (by
        rw [hd] at hw
        simp only [integerPartial_apply]
        rw [hw]
        have hn : residueMap (MvPolynomial.pderiv 0 sextic) ≠ 0 := normal_ne_zero
        field_simp
        ring)
  apply certificate_of_normalized D (Fin.cases N₀ N) Q hlegal
  · simpa only [HodgeTestbed.directional,Fin.sum_univ_succ,Fin.cases_zero,
      Fin.cases_succ,integerPartial_apply,mul_comm] using hnormal
  · simpa only [HodgeTestbed.divergenceNumerator,HodgeTestbed.divergence,
      HodgeTestbed.directional,residueDivNum,Fin.sum_univ_succ,Fin.cases_zero,
      Fin.cases_succ,integerPartial_apply,mul_comm] using hdiv

end CyclePhysical
#print axioms CyclePhysical.certificate_of_residue_solution
