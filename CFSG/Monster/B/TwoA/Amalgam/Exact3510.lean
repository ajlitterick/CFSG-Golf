module

public import CFSG.Monster.B.TwoA.Amalgam.Exact3510Core
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeType

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_order_three_common_neighbors_exact_3510 :
    (∀ v w : CVert, w ∈ sphereThree v →
      (cgraph.induce (cgraph.commonNeighbors v w)).Connected ∧
      (∀ [Fintype (cgraph.commonNeighbors v w)]
        [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj],
        (cgraph.induce (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126) ∧
      (cgraph.commonNeighbors v w).ncard = 3510 ∧
      (sphereThree v).ncard = 2370830336 ∧
      (∀ s ∈ vStab v ⊓ vStab w, (∀ x ∈ cgraph.commonNeighbors v w, cvMul x s = x) → s = 1) ∧
      Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = 129123503308800) ∧
    ∀ μ₃ : ℕ, (∀ v w : CVert, w ∈ sphereThree v → (cgraph.commonNeighbors v w).ncard = μ₃) →
      μ₃ = 3510 := by
  have hType : ∀ ⦃v w u z : CVert⦄, w ∈ sphereThree v → u ∈ cgraph.commonNeighbors v w →
      z ∈ cgraph.commonNeighbors v w → u ≠ z → ¬cgraph.Adj u z → z ∈ sphereThree u :=
    fun _ _ _ _ hw hu hz huz hna => mem_sphereThree_of_mem_commonNeighbors hw hu hz huz hna
  refine ⟨fun v w hw => ⟨cn_connected hType hw, fun {_ _} => cn_isSRGWith hType hw,
    ncard_commonNeighbors_eq_3510 hType hw, ncard_sphereThree_eq hType v,
    (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.1,
    natCard_pairStab_eq hType hw⟩, fun μ₃ hμ => ?_⟩
  obtain ⟨w, hw⟩ := sphereThree_nonempty exists_rootModel cv0
  rw [← hμ cv0 w hw, ncard_commonNeighbors_eq_3510 hType hw]

end CFSG.Monster.B.TwoA.Amalgam
