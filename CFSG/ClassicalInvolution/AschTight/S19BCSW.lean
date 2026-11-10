module

public import CFSG.ClassicalInvolution.AschTight.S19BCtl
public import CFSG.ClassicalInvolution.AschTight.S1911C11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}


theorem inf_sec19BPrime_eq_bot (hd : Sec19DataT p f K z S W L t V) :
    W ⊓ sec19BPrime K S W L = ⊥ := by
  obtain ⟨RL, hRL, hWRL, -, -⟩ := S1911.exists_sylow_member hd
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxN : x ∈ Subgroup.normalizer (RL : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.1)
  have hxRL : x ∈ Subgroup.centralizer (RL : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (S1916.commute_of_mem_centralizerModOdd hx.2.2 hRL.1 hRL.2.1 hxN hy).symm
  have h := S1911.inf_centralizer_inf_eq_bot hd hRL
  have hmem : x ∈ W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (RL : Set G) := ⟨⟨hx.1, hx.2.1.1.2⟩, hxRL⟩
  rw [h] at hmem
  exact hmem

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
