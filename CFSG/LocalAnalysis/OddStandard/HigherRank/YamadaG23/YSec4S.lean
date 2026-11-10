module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ExtremalTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


@[expose] def Sec42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), BranchA e → IsSylowIn 2 ⊤ s.T₂

@[expose] def Sec44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), BranchA e →
      ∃ N : Subgroup G, N ≤ s.T₂ ∧ SecProp s.T₂ N (fun Y _ _ _ => IsCyclic Y) ∧
        ∀ x : G, IsExtremalConj s.T₂ s.t x → x ∉ N

@[expose] def Sec4False : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), BranchA e → False

theorem transfer_of_isSylowIn [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {P N : Subgroup G} (hsyl : IsSylowIn 2 ⊤ P) (hNP : N ≤ P)
    (hsec : SecProp P N (fun Y _ _ _ => IsCyclic Y)) {t : G} (ht : orderOf t = 2)
    (hext : ∀ x : G, IsExtremalConj P t x → x ∉ N) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 P := hsyl.2.1
  have hidx : ¬ 2 ∣ P.index := by
    have h := hsyl.2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 G, (Q : Subgroup G) = P :=
    ⟨hpg.toSylow hidx, IsPGroup.toSylow_coe hpg hidx⟩
  subst hQ
  obtain ⟨hn, hcyc⟩ := hsec
  haveI := hn
  exact transfer_extremal_cyclic hnonab Q hNP hcyc ht hext

theorem sec4False_of (h42 : Sec42) (h44 : Sec44) : Sec4False := by
  intro G _ _ L hS hL s e hA
  haveI : IsSimpleGroup G := hS.std.simple
  obtain ⟨N, hNle, hsec, hext⟩ := h44 G L hS hL s e hA
  exact transfer_of_isSylowIn hS.std.nonab (h42 G L hS hL s e hA) hNle hsec s.t_order hext

end CFSG.OddStandard.HigherRank.YamadaG23
