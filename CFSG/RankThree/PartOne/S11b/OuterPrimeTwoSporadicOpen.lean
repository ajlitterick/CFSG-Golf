module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicBridgeA
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicBridgeB

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms


theorem sporadicOuterSmallSimple_of_simple
    (hopen : SporadicOuterOrderLeTwoSimple) (s : TauCeti.SporadicName) :
    SporadicOuterSmallSimple s := by
  have h7 : ∀ s, (s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M) →
      SporadicOuterSmallSimple s := fun s hs T _ _ _ hnonab hT =>
    Or.inl (lt_of_le_of_lt (hopen s hs T hnonab hT) (by norm_num))
  cases s
  · exact sporadicOuterSmall_M11.toSimple
  · exact sporadicOuterSmall_M12.toSimple
  · exact sporadicOuterSmall_M22.toSimple
  · exact sporadicOuterSmall_M23.toSimple
  · exact sporadicOuterSmall_M24.toSimple
  · exact sporadicOuterSmall_J1.toSimple
  · exact sporadicOuterSmall_J2.toSimple
  · exact sporadicOuterSmall_J3.toSimple
  · exact sporadicOuterSmall_J4.toSimple
  · exact sporadicOuterSmall_HS.toSimple
  · exact sporadicOuterSmall_McL.toSimple
  · exact sporadicOuterSmall_He.toSimple
  · exact sporadicOuterSmall_Ru.toSimple
  · exact sporadicOuterSmall_Suz.toSimple
  · exact sporadicOuterSmall_ONan.toSimple
  · exact h7 .Co1 (by simp)
  · exact h7 .Co2 (by simp)
  · exact sporadicOuterSmall_Co3.toSimple
  · exact sporadicOuterSmall_Fi22.toSimple
  · exact sporadicOuterSmall_Fi23.toSimple
  · exact sporadicOuterSmall_Fi24Prime.toSimple
  · exact h7 .HN (by simp)
  · exact h7 .Ly (by simp)
  · exact h7 .Th (by simp)
  · exact h7 .B (by simp)
  · exact h7 .M (by simp)

end CFSG.RankThree.PartOne
