module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem mem_of_central_of_pRank_le_two (hp : p.Prime) {Q B : Subgroup A}
    (hQ : Open.pRank p Q ≤ 2) (hBQ : B ≤ Q) (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    {w : A} (hwQ : w ∈ Q) (hwp : w ^ p = 1) (hw : ∀ q ∈ Q, q * w = w * q) : w ∈ B := by
  by_contra hwB
  have hcomm : ∀ a ∈ B, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a w from hw a (hBQ ha)) k).eq
  have hel := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hB
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hwp) hcomm
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hel
  have hlt : B < B ⊔ zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun h => hwB ?_
    rw [h]
    exact mem_sup_right (mem_zpowers w)
  have hcard := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [hBcard, hk] at hcard
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
    omega
  have hle : k ≤ Open.pRank p Q :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt
      (sup_le hBQ (zpowers_le.mpr hwQ)) hel hk
  omega

theorem pCore_le_sylow {X : Type*} [Group X] [Fact p.Prime] (S : Sylow p X) :
    CFSG.pCore p X ≤ S := by
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hsup : IsPGroup p ↥(CFSG.pCore p X ⊔ (S : Subgroup X)) :=
    (CFSG.pCore_isPGroup (p := p) (G := X)).to_sup_of_normal_left S.isPGroup'
  have h := S.is_maximal' hsup le_sup_right
  rw [← h]
  exact le_sup_left


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
