module

public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.Adapters.GlaubermanZJ
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]


theorem thompsonSubgroup_ne_bot {S : Subgroup G} (hS : S ≠ ⊥) : Open.thompsonSubgroup S ≠ ⊥ := by
  obtain ⟨A, hA⟩ := thompsonAbelianSubgroups_nonempty (G := G) S
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS
  have hcard := hA.2.2 (Subgroup.zpowers (x : G)) (Subgroup.zpowers_le.mpr x.2) inferInstance
  intro hbot
  have hAJ : A ≤ CFSG.thompsonSubgroup S := le_sSup hA
  rw [← Adapters.leanEval_thompsonSubgroup_eq, hbot, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot, Nat.card_zpowers] at hcard
  exact hx1 (Subtype.ext (orderOf_eq_one_iff.mp (le_antisymm hcard (orderOf_pos _))))


theorem map_center_ne_bot {S : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    (Subgroup.center S).map S.subtype ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot _).mpr hS1
  have hcnt : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective]
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hcnt

namespace TwoLocalPair

variable {M H : Subgroup G}

theorem thompsonJ_twoCore_ne (h : TwoLocalPair M H) :
    Quasithin.thompsonJ (pCoreOf 2 H) ≠ Quasithin.thompsonJ (pCoreOf 2 M) :=
  h.ne_of_char (Quasithin.B6.thompsonJ_le _)
    (QuasithinUnique.Setup.thompsonJ_ne_bot (pCoreOf_isPGroup 2 H) h.twoCore_H_ne_bot)
    (QuasithinUnique.Setup.characteristic_thompsonJ _) (Quasithin.B6.thompsonJ_le _)
    (QuasithinUnique.Setup.characteristic_thompsonJ _)


theorem not_thompsonJ_le_twoCore_M (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ Quasithin.thompsonJ (pCoreOf 2 H) ≤ pCoreOf 2 M := fun hle =>
  h.thompsonJ_twoCore_ne (Quasithin.B6.thompsonJ_eq_of_le hle (h.twoCore_M_le hS)).symm

theorem exists_isMaxElemAbelian_not_le (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ∃ A : Subgroup G, Quasithin.IsMaxElemAbelian (pCoreOf 2 H) A ∧ ¬ A ≤ pCoreOf 2 M := by
  by_contra hcon
  refine h.not_thompsonJ_le_twoCore_M hS (iSup₂_le fun A hA => ?_)
  by_contra hAQ
  exact hcon ⟨A, hA, hAQ⟩


end TwoLocalPair

namespace D1Escape

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}


theorem twoCore_H_ne_bot (h : D1Escape p P M H R) : pCoreOf 2 H ≠ ⊥ :=
  h.toTwoLocalPair.twoCore_H_ne_bot


theorem exists_isMaxElemAbelian_not_le (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ∃ A : Subgroup G, Quasithin.IsMaxElemAbelian (pCoreOf 2 H) A ∧ ¬ A ≤ pCoreOf 2 M :=
  h.toTwoLocalPair.exists_isMaxElemAbelian_not_le hS


end D1Escape


end CFSG.AGLEmbedding
