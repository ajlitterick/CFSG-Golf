module

public import CFSG.ClassicalInvolution.Q3.Q3PBal
public import CFSG.ClassicalInvolution.Q3.Q3MApp
public import CFSG.ClassicalInvolution.Q3.Q3MEnd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Q3.M
open scoped MatrixGroups

namespace M

theorem three_decomp {X : Type} [Group X] {T D N : Subgroup X} {z : X}
    (hTN : T ≤ N) (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t) (hNTD : N ≤ T ⊔ D)
    (h2 : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1) (hzN : z ∈ N) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set X) ⊓ N, (∃ k : ℕ, c ^ (3 ^ k) = 1) →
      ∃ u ∈ (Subgroup.centralizer ({z} : Set X) ⊓ N) ⊓ T,
        ∃ v ∈ (Subgroup.centralizer ({z} : Set X) ⊓ N) ⊓ D, c = u * v := by
  intro c hc ⟨k, hk⟩
  obtain ⟨t, ht, d, hd, hcd⟩ := exists_mul_of_mem_sup hcomm (hNTD hc.2)
  obtain ⟨t₀, ht₀, d₀, hd₀, hzd⟩ := exists_mul_of_mem_sup hcomm (hNTD hzN)
  have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc.1 z (Set.mem_singleton z)
  have hc' : t * d * (t₀ * d₀) = t₀ * d₀ * (t * d) := by
    rw [hcd, hzd] at hzc
    exact hzc.symm
  have hk' : (t * d) ^ (3 ^ k) = 1 := by rw [← hcd]; exact hk
  have ht_comm := commute_of_three_element hcomm h2 ht₀ hd₀ ht hd hc' hk'
  have htz : t ∈ Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh, hzd]
    exact ht_comm.symm
  have htCg : t ∈ Subgroup.centralizer ({z} : Set X) ⊓ N := ⟨htz, hTN ht⟩
  refine ⟨t, ⟨htCg, ht⟩, t⁻¹ * c, ⟨?_, ?_⟩, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htCg) hc
  · have : t⁻¹ * c = d := by rw [hcd]; group
    rw [this]
    exact hd

end M


end CFSG.ClassicalInvolution.Q3
