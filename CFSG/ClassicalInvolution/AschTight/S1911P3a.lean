module

public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.ClassicalInvolution.AschTight.S1911FusG
public import CFSG.ClassicalInvolution.AschTight.S1911SecA

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem false_of_le_inf_centralizer (hd : Sec19Data p f K z S W) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ CoreAssembly.conjClass K) (hJ₂ : J₂ ∈ CoreAssembly.conjClass K) (hJne : J₁ ≠ J₂)
    {u₁ u₂ : G} (hI₁ : IsUniqueInvolution J₁ u₁) (hI₂ : IsUniqueInvolution J₂ u₂)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R) (hRJ₂ : R ≤ J₂) (hRz : R ≤ Subgroup.centralizer ({u₁} : Set G)) :
    False := by
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRJ₂ hRz)
  have hu₂V : u₂ ∈ V := hRV (mem_of_le_member hI₂ hRJ₂ hR2 (by omega))
  have htwin : J₂ ∉ twinSet (CoreAssembly.conjClass K) J₁ := by
    rintro ⟨-, u, hu₁, hu₂⟩
    exact hJne (eq_of_isUniqueInvolution_member htb hJ₁ hJ₂ hu₁ hu₂)
  have hcard : Nat.card R ≤ Nat.card V := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f hd.tight.branch.odd hd.tight.branch.five G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V hV hu₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · exact not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ₂ hJ₁ hJne.symm hV4
      (hV.1.trans inf_le_left)
      ((hV.1.trans inf_le_right).trans (centralizer_le_normalizer_member htb hJ₁ hI₁))


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
