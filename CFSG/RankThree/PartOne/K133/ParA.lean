module

public import CFSG.RankThree.PartOne.S13K.Pair134Basic
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_zpowers_le_theta {p : ℕ} {E I : Subgroup G} {c : G}
    (hc : c ∈ thetaQuotientCentralizer p E I) :
    ⁅I, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore p) I := by
  rw [Subgroup.commutator_le]
  intro y hy z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hcn : c ^ n ∈ thetaQuotientCentralizer p E I := Subgroup.zpow_mem _ hc n
  obtain ⟨-, -, hθ⟩ := mem_thetaQuotientCentralizer_iff.1 hcn
  have e1 : ⁅y, c ^ n⁆ = (c ^ n * y * (c ^ n)⁻¹ * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e1]
  exact (inSubgroup (aschbacherSolvableCore p) I).inv_mem (hθ y hy)


end CFSG.RankThree.PartOne.K133
