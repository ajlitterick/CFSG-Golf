module

public import CFSG.ClassicalInvolution.Q3.Q3CPLocC

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]


section Dictionary

variable [Finite G] {K : Subgroup G} {z : G}


omit [Finite G] in
theorem mem_of_isSylow2In_of_isUniqueInvolution {M P : Subgroup G} {y : G}
    (hy : IsUniqueInvolution M y) (hP : IsSylow2In P M) : y ∈ P := by
  have hc : ∀ m ∈ M, m * y = y * m := by
    intro m hm
    have hmy : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hy.mem) (M.inv_mem hm)
    have hsq : (m * y * m⁻¹) * (m * y * m⁻¹) = 1 := by
      calc (m * y * m⁻¹) * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
        _ = 1 := by rw [hy.sq]; group
    rcases hy.unique _ hmy hsq with h1 | h1
    · exfalso
      apply hy.ne_one
      have : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [this, h1]
      group
    · calc m * y = (m * y * m⁻¹) * m := by group
        _ = y * m := by rw [h1]
  have h2 : IsPGroup 2 (Subgroup.zpowers y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hy.sq) hy.ne_one]
    norm_num
  have hyc : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => hc h (hP.1 hh)
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hyc).trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers y ⊔ P) := h2.to_sup_of_normal_right' hP.2.1 hnorm
  have hle : Subgroup.zpowers y ⊔ P ≤ M := sup_le (Subgroup.zpowers_le.mpr hy.mem) hP.1
  have heq := hP.2.2 (Subgroup.zpowers y ⊔ P) hle hsup le_sup_right
  exact heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end Dictionary

section Branch


end Branch

end CFSG.ClassicalInvolution.Q3.Q3CP
