module

public import CFSG.CharacterTheory.Wreathed.BrauerWongSubgroup
public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u

variable {G : Type u} [Group G]


variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))


variable [Finite G]


theorem eq_centralizer_mul_pPrimeCore_of_base_order_two (hn : 2 ≤ n)
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    {z : G} (hz : z ∈ modelCenter S e) (g : G) :
    ∃ c ∈ Subgroup.centralizer {z}, ∃ o ∈ CFSG.pPrimeCore 2 G, g = c * o := by
  have hcyc : IsCyclic (modelCenter S e) := by
    rw [modelCenter_eq_zpowers]
    infer_instance
  have hAC : modelCenter S e ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := modelCenter_conj S e hn hc hs
    calc
      s * c = s * (s⁻¹ * c * s) := by rw [h]
      _ = c * s := by group
  obtain ⟨-, hfac⟩ := cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core S
    (modelCenter S e) (modelCenter_le_sylow S e) hAC
    (fun c hc g hg => modelCenter_isolated_of_base_order_two hn S e hcard hc g hg)
  obtain ⟨r, hr, c, hc, rfl⟩ := hfac g
  rw [weakClosure_oddCore_eq_pPrimeCore] at hr
  refine ⟨c, ?_, c⁻¹ * r * c, ?_, by group⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc z hz).symm
  · have := (CFSG.pPrimeCore_normal (p := 2) (G := G)).conj_mem r hr c⁻¹
    simpa using this

end CFSG.Wreathed.BrauerWong
