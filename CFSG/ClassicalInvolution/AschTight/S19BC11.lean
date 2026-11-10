module

public import CFSG.ClassicalInvolution.AschTight.S19BFus
public import CFSG.ClassicalInvolution.AschTight.S19BEnd
public import CFSG.ClassicalInvolution.AschTight.S1911C11
public import CFSG.ClassicalInvolution.AschTight.S19BCtl

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}


omit [IsSimpleGroup G] in
theorem conj_mem_T {a c : G} (ha : a ∈ sec19T K z S)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcS : c * a * c⁻¹ ∈ (S : Subgroup G)) :
    c * a * c⁻¹ ∈ sec19T K z S := by
  have htop : conjSub c (⊤ : Subgroup G) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_conjSub_iff.mpr (Subgroup.mem_top _)
  have hle := Hall196.conjSub_centralizerModOdd_le (H := ⊤) (L := sec19X K z)
    (Hall196.centralizer_le_normalizer_sec19X K z hc) htop
  exact ⟨hcS, hle (conj_mem_conjSub ha.2)⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
