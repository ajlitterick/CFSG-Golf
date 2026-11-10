module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)


variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_card_inf_nine {L E : Subgroup G} (hE : Late.IsE27 E)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9) :
    (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E := by
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using hexpE x x.2.1)⟩
  obtain ⟨x, hxEL, hxC⟩ : ∃ x ∈ E ⊓ L, x ∉ Sec4.thetaQuotCentralizer L := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ L ≤ E ⊓ Sec4.thetaQuotCentralizer L ⊓ L := fun y hy =>
      ⟨⟨hy.1, hcon y hy⟩, hy.2⟩
    have h1 := (Subgroup.card_le_of_le hle).trans
      (card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right)
    rw [hEL9, hZ] at h1
    norm_num at h1
  exact eq_of_card_nine_lt hE.2 (sup_le inf_le_left inf_le_left) le_sup_left hB9
    (Subgroup.mem_sup_right hxEL) fun h => hxC h.2


end CFSG.RankThree.PartTwo.Sec12
