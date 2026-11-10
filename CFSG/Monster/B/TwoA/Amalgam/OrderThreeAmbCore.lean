module

public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.E6.StdF4WeylPair

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem triType_eq_of_adj
    {v w u z : CVert} (hw : w ∈ sphereThree v)
    (hu : u ∈ cgraph.commonNeighbors v w) (hz : z ∈ cgraph.commonNeighbors v w)
    (huz : cgraph.Adj u z) : triType v u z = 44352 := by
  obtain ⟨M, hL⟩ := exists_rootModel u
  have hvu : v ∈ cgraph.neighborSet u :=
    (cgraph.mem_neighborSet u v).2 (hu.1 : cgraph.Adj v u).symm
  have hwu : w ∈ cgraph.neighborSet u :=
    (cgraph.mem_neighborSet u w).2 (hu.2 : cgraph.Adj w u).symm
  have hzu : z ∈ cgraph.neighborSet u := (cgraph.mem_neighborSet u z).2 huz
  have h3 : orbSize (M.pt ⟨v, hvu⟩) (M.pt ⟨w, hwu⟩) = 2097152 :=
    (M.labelThree_dist_iff hL ⟨v, hvu⟩ ⟨w, hwu⟩).1 hw
  have ho : orderOf ((M.iv ⟨v, hvu⟩ : stdGroup) * M.iv ⟨w, hwu⟩) = 3 := by
    rw [← orderOf_injective (SemidirectProduct.inl : stdGroup →* GStar)
      SemidirectProduct.inl_injective, map_mul]
    exact (orderOf_eq_three_iff (M.pt_mem _) (M.pt_mem _)).2 h3
  have hvz : cgraph.Adj v z := hz.1
  have hwz : cgraph.Adj w z := hz.2
  have hzv : (⟨z, hzu⟩ : cgraph.neighborSet u) ≠ ⟨v, hvu⟩ := fun e =>
    hvz.ne (congrArg Subtype.val e).symm
  have hzw : (⟨z, hzu⟩ : cgraph.neighborSet u) ≠ ⟨w, hwu⟩ := fun e =>
    hwz.ne (congrArg Subtype.val e).symm
  have hcv := (M.adj_iff ⟨z, hzu⟩ ⟨v, hvu⟩ hzv).1 hvz.symm
  have hcw := (M.adj_iff ⟨z, hzu⟩ ⟨w, hwu⟩ hzw).1 hwz.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hwp⟩ :=
    standard_F4_Weyl_pair_orbit_and_opposite_slice
  have h44 := (hwp _ _ (M.iv ⟨v, hvu⟩).2 (M.iv ⟨w, hwu⟩).2 ho _ (M.iv ⟨z, hzu⟩).2 hcv hcw).1
  rw [triType_swap_left u v z]
  exact (M.triType_eq_orbSize ⟨v, hvu⟩ ⟨z, hzu⟩).trans h44

section Type3

variable (hType : ∀ ⦃v w u z : CVert⦄, w ∈ sphereThree v → u ∈ cgraph.commonNeighbors v w →
  z ∈ cgraph.commonNeighbors v w → u ≠ z → ¬cgraph.Adj u z → z ∈ sphereThree u)

include hType in
theorem triType_eq_of_not_adj
    {v w u z : CVert} (hw : w ∈ sphereThree v)
    (hu : u ∈ cgraph.commonNeighbors v w) (hz : z ∈ cgraph.commonNeighbors v w) (hne : u ≠ z)
    (hna : ¬cgraph.Adj u z) : triType v u z = 2097152 := by
  obtain ⟨M, hL⟩ := exists_rootModel v
  exact (M.triType_eq_orbSize ⟨u, hu.1⟩ ⟨z, hz.1⟩).trans
    ((M.labelThree_dist_iff hL ⟨u, hu.1⟩ ⟨z, hz.1⟩).1 (hType hw hu hz hne hna))

namespace RootModel

variable {v w : CVert} (M : RootModel v)

include hType in
theorem orbSize_of_mem_commonNeighbors
    (hw : w ∈ sphereThree v) {u z : cgraph.neighborSet v}
    (hu : (u : CVert) ∈ cgraph.commonNeighbors v w) (hz : (z : CVert) ∈ cgraph.commonNeighbors v w)
    (hne : u ≠ z) :
    (cgraph.Adj u z → orbSize (M.pt u) (M.pt z) = 44352) ∧
      (¬cgraph.Adj u z → orbSize (M.pt u) (M.pt z) = 2097152) := by
  have hne' : (u : CVert) ≠ z := fun e => hne (Subtype.ext e)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (M.triType_eq_orbSize u z).symm.trans (triType_eq_of_adj hw hu hz h)
  · exact (M.triType_eq_orbSize u z).symm.trans (triType_eq_of_not_adj hType hw hu hz hne' h)


end RootModel

end Type3

end CFSG.Monster.B.TwoA.Amalgam
