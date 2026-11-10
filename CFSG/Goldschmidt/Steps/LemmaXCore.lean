module

import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

namespace LemmaX

theorem two_dvd_card_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  have : Nontrivial K := Quasisimple.nontrivial hK
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

theorem layer_structure {Q : Type} [Group Q] [Finite Q] (hO : goldschmidtOddCore Q = ⊥)
    (P : Sylow 2 Q) {B : Subgroup Q} (ha : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hb : B = CFSG.Open.pCore 2 Q ⊔
      Subgroup.closure {t | t ∈ (P : Subgroup Q) ⊓ goldschmidtLayer Q ∧ t ^ 2 = 1})
    (hC2 : CFSG.Open.pCore 2 Q ≤ Subgroup.center Q) (K : Subgroup Q) (hK : IsComponentOf K ⊤)
    (hfaith : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set Q) → b = 1) :
    K = ⊤ ∧ Subgroup.center Q = ⊥ ∧ ∀ t ∈ (P : Subgroup Q), t ^ 2 = 1 → t ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2B : CFSG.Open.pCore 2 Q ≤ B := hb ▸ le_sup_left
  have hO2 : CFSG.Open.pCore 2 Q = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    exact Subgroup.mem_bot.2
      (hfaith p (hO2B hp) (Subgroup.center_le_centralizer _ (hC2 hp)))
  have hL : goldschmidtLayer Q = ⊤ := by rw [← ha, hO2, bot_sup_eq]
  have hinv : ∀ t ∈ (P : Subgroup Q), t ^ 2 = 1 → t ∈ B := by
    intro t ht ht2
    rw [hb]
    refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨ht, ?_⟩, ht2⟩)
    rw [hL]
    exact Subgroup.mem_top t
  have hone : ∀ K₂ : Subgroup Q, IsComponentOf K₂ ⊤ → K₂ = K := by
    intro K₂ hK₂
    by_contra hne
    have hsub := Components.mathlib_subnormal_of_chain hK₂.2.1 Subgroup.IsSubnormal.top
    obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hsub
    obtain ⟨s, hsR, hs2⟩ := PropHSetup.exists_orderOf_eq_two R.isPGroup'
      (R.ne_bot_of_dvd_card (two_dvd_card_of_isQuasisimple hK₂.2.2))
    have hs2' : orderOf (s : Q) = 2 := (Subgroup.orderOf_coe s).trans hs2
    have hsP : (s : Q) ∈ (P : Subgroup Q) := by
      have h1 : (s : Q) ∈ (R : Subgroup K₂).map K₂.subtype := ⟨s, hsR, rfl⟩
      rw [hR] at h1
      exact h1.1
    have hsB : (s : Q) ∈ B := hinv _ hsP (hs2' ▸ pow_orderOf_eq_one (s : Q))
    have hsC : (s : Q) ∈ Subgroup.centralizer (K : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b Q K₂ K hK₂ hK hne) s.2
    have h1 := hfaith _ hsB hsC
    rw [h1, orderOf_one] at hs2'
    exact absurd hs2' (by norm_num)
  have hKtop : K = ⊤ := by
    rw [← hL]
    refine le_antisymm (le_sSup hK) (sSup_le fun K₂ hK₂ => (hone K₂ hK₂).le)
  have hZ : Subgroup.center Q = ⊥ := by
    obtain ⟨-, hZE, -⟩ := N8d Q hO
    rw [eq_bot_iff, ← hO2]
    intro x hx
    have hxL : x ∈ goldschmidtLayer Q := by
      rw [hL]
      exact Subgroup.mem_top x
    apply hZE
    exact ⟨⟨x, hxL⟩,
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hx y), rfl⟩
  exact ⟨hKtop, hZ, hinv⟩


variable {Y : Type} [Group Y] [Finite Y]

theorem oddCoreOf_le {E J M : Subgroup Y} (hEab : IsMulCommutative E)
    (hEexp : ∀ e ∈ E, e ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hCJ : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set Y) ≤ J) (hEM : E ≤ M) :
    oddCoreOf M ≤ J := by
  refine le_of_forall_inf_centralizer_le hEab hEexp hE4 ?_ ?_
    fun e he he1 => inf_le_right.trans (hCJ e he he1)
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨e, hEM he⟩ * o * ⟨e, hEM he⟩⁻¹,
        (goldschmidtOddCore_normal M).conj_mem o ho _, rfl⟩
    · rintro ⟨o, ho, hoe⟩
      refine ⟨⟨e, hEM he⟩⁻¹ * o * ⟨e, hEM he⟩, ?_, ?_⟩
      · have := (goldschmidtOddCore_normal M).conj_mem o ho ⟨e, hEM he⟩⁻¹
        simpa using this
      · have hoe' : (o : Y) = e * x * e⁻¹ := hoe
        show (e : Y)⁻¹ * o * e = x
        rw [hoe']
        group
  · rw [oddCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
    exact OddCore.odd_card M


end LemmaX

end CFSG.Goldschmidt
