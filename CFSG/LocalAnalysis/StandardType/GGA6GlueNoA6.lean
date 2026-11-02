module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem a6glue_not_quotA6_of_card {G : Type} [Group G] {X : Subgroup G}
    (h : Nat.card (↥X ⧸ Subgroup.center ↥X) ≠ 360) :
    ¬ Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  apply h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem a6glue_not_quotA6_of_fieldAt
    {G : Type} [Group G] {Q : ℕ} {X : Subgroup G} (h : CFSG.StandardType.GGCompFieldAt Q X) :
    ¬ Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨lab, hlab, hc, hdeg, h1, h2, h3, hhas, R, instR, hR, ⟨θ⟩⟩ := h
  let : Group R := instR
  rintro ⟨e⟩
  have hcard : Nat.card R = 360 := by
    rw [← Nat.card_congr θ.toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide
  have htag : lab.tag ≠ .B2der := by
    intro hB
    simp [markChar, hB] at hc
  exact ggMarkedModel_card_ne_three_sixty htag hR hcard

end CFSG.StandardType.A6Red
