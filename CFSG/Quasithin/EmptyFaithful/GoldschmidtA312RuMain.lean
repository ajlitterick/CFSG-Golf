module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuCases
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuQuot
public import CFSG.Quasithin.Background.A312SporGen
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuPerf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.Quasithin.A312Ru

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

section Rows

variable {Γ : Type} [Group Γ]

theorem card_pCore_of_pCoreOf {Y : Subgroup Γ} {k : ℕ}
    (h : Nat.card (CFSG.Open.pCoreOf 2 Y) = k) : Nat.card (CFSG.pCore 2 ↥Y) = k := by
  have h1 : CFSG.Open.pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := rfl
  rwa [h1, Subgroup.card_map_of_injective Y.subtype_injective] at h

end Rows

theorem ru_row_one :
    Nat.card (CFSG.pCore 2 ↥(ruCtx.Y 1)) = 2 ^ 11 ∧
      ∀ (N : Subgroup ↥(ruCtx.Y 1)) [N.Normal], IsPGroup 2 (↥(ruCtx.Y 1) ⧸ N) →
        Nat.card (↥(ruCtx.Y 1) ⧸ N) ≤ 2 := by
  obtain ⟨m, hm, h1, h2, h3⟩ := ru_row 1 (by norm_num)
  have hc : Nat.card (ruCtx.Y 1) = 245760 := by
    rw [ru_member_card 1 (by norm_num)]; rfl
  simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exfalso; simp only at h1; omega)
    | exact ⟨card_pCore_of_pCoreOf (by simpa using h2), fun N _ hp => h3 N hp⟩

theorem ru_row_two :
    Nat.card (CFSG.pCore 2 ↥(ruCtx.Y 2)) = 2 ^ 11 := by
  obtain ⟨m, hm, h1, h2, -⟩ := ru_row 2 (by norm_num)
  have hc : Nat.card (ruCtx.Y 2) = 344064 := by
    rw [ru_member_card 2 (by norm_num)]; rfl
  simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exfalso; simp only at h1; omega)
    | exact card_pCore_of_pCoreOf (by simpa using h2)

end CFSG.Quasithin.A312Ru
