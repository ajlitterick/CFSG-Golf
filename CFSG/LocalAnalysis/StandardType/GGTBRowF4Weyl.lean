module

public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Frame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggF4Row_weylOfType
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hL : GGInnerDiagOnLabel GGTableBF4Label p Bs L) :
    GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  exact ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ (ggF4Row_frame hHyp hL hN)

end CFSG.StandardType

end
