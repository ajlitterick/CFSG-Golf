module

public import CFSG.Quasithin.H13.NQCatLieCentralRank1
public import CFSG.Quasithin.H13.NQCatLieCentralL3
public import CFSG.Quasithin.H13.NQCatLieCentralU3
public import CFSG.Quasithin.H13.NQCatLieCentralSp4
public import CFSG.Quasithin.H13.NQCatLieCentralG2
public import CFSG.Quasithin.H13.NQCatLieCentralD4
public import CFSG.Quasithin.H13.NQCatLieCentralF4
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.QuasithinUnique.Setup.X6

theorem centralIndex_of_isLieChar2Big
    {S : Type} [Group S] [Finite S] (hL : IsLieChar2Big S) : CentralIndex S := by
  obtain ⟨k, hk, h⟩ := hL
  have hk4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases h with h | h | h | h | h | h | h | h
  ·
    obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated h
    exact centralIndex_linear (.linear k hk e)
  ·
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have : CharP F 2 := LieMult.charP_two_of_card hF
    exact CentralIndex.of_mulEquiv (e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 F))
      (L3.centralIndex_l3 (hF ▸ hk4))
  ·
    exact U3.centralIndex_psu3 hk h
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : CharP K 2 := LieMult.charP_two_of_card hK
    exact CentralIndex.of_mulEquiv e (Sp4.centralIndex_projSp4 (hK ▸ hk4))
  ·
    obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_G2_model h
    exact CentralIndex.of_mulEquiv e (G2.centralIndex_g2 (hF ▸ hk4))
  ·
    obtain ⟨hn, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model h
    have : CharP K 2 := CFSG.Quasithin.B42D4.charP_two_of_card hn hK
    exact CentralIndex.of_mulEquiv e (D4.centralIndex_d4 σ hk hK hσ)
  ·
    obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := h
    exact CentralIndex.of_mulEquiv e (centralIndex_suzuki ha (by rw [hF, hf]))
  ·
    obtain ⟨-, -, -, -, ⟨a, ha, hka⟩, hiso⟩ := ReeTag.large_Ree_model_Schreier S 2 k h
    obtain ⟨-, a', hka', ⟨K, _, _, hK, he⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := k) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
    have haa' : a' = a := by omega
    subst haa'
    obtain ⟨e⟩ := hiso a' K hka' hK he
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hka']
    exact CentralIndex.of_mulEquiv e (F4.centralIndex_f4 ha hK')

theorem lieCentralIndexFact_holds :
    LieCentralIndexFact := fun _ _ _ hL => centralIndex_of_isLieChar2Big hL

end CFSG.Quasithin.H13.NQCat.LieCentral
