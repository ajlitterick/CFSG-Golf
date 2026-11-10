module

public import CFSG.GH74.M12.HypT2
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Data

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover

set_option maxRecDepth 100000 in
theorem bfT_center : ∀ s ∈ BT, (∀ t ∈ BT, tmul s t = tmul t s) → s = tid ∨ s = JT := by
  decide

theorem bfS'_center {y : G12} (hy : y ∈ bfS')
    (hc : ∀ x ∈ bfS', x * y = y * x) : y = 1 ∨ y = Jelt := by
  have hty : tbl y.1 ∈ BT := mem_bfS_iff.1 hy
  have hcent : ∀ t ∈ BT, tmul (tbl y.1) t = tmul t (tbl y.1) := by
    intro t ht
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 ht
    have hσ : bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) ∈ bfS := bfElt_mem _ _ _ _
    have hs : (⟨_, bfS_le_M12 hσ⟩ : G12) ∈ bfS' := hσ
    have h3 := congrArg tbl (congrArg Subtype.val (hc _ hs))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, tbl_mul, tbl_mul, tbl_bfElt, ← hn] at h3
    exact h3.symm
  rcases bfT_center _ hty hcent with h | h
  · exact Or.inl (Subtype.ext (tbl_injective (by rw [h, Subgroup.coe_one, tbl_one])))
  · exact Or.inr (Subtype.ext (tbl_injective (by rw [h, ← tbl_bfJ]; rfl)))

theorem exists_conj_Jelt_m12Rep1 :
    ∃ c ∈ NativeSporadic.M12, (Jelt : Equiv.Perm (Fin 12)) = c * m12Rep1 * c⁻¹ := by
  have hord : orderOf (Jelt : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact orderOf_Jelt
  obtain ⟨r, hr, c, hc, hJ⟩ := m12_involution_cover.1 (Jelt : Equiv.Perm (Fin 12))
    (by simp) hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨c, hc, hJ⟩
  · exfalso
    have hS : bfS ≤ centralizerIn NativeSporadic.M12 (Jelt : Equiv.Perm (Fin 12)) := fun σ hσ => by
      rw [mem_centralizerIn]
      exact ⟨bfS_le_M12 hσ, congrArg Subtype.val (bfS'_comm_Jelt (s := ⟨σ, bfS_le_M12 hσ⟩) hσ)⟩
    have hcard :
        Nat.card (centralizerIn NativeSporadic.M12 (Jelt : Equiv.Perm (Fin 12))) = 240 := by
      rw [hJ, centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective,
        card_centralizerIn_m12Rep2]
    have h64 : 64 ∣ 240 := by
      rw [← card_bfS, ← hcard]
      exact Subgroup.card_dvd_of_le hS
    omega


end CFSG.EvenSporadicStandard.M12Std
