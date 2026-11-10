module

public import CFSG.Quasithin.EmptyFaithful.S14117Coprime

public section

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

variable {A : Type*} [Group A]

theorem oTwoUpper_commutator_sup_le {B P : Subgroup A} (hP : IsPGroup 2 P)
    (hPB : P ≤ Subgroup.normalizer (B : Set A)) :
    oTwoUpper (⁅B, P⁆ ⊔ P) ≤ ⁅B, P⁆ := by
  have hnormK : P ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup A) : Set A) :=
    le_normalizer_commutator_of_le hPB Subgroup.le_normalizer
  have hmul : ((⁅B, P⁆ ⊔ P : Subgroup A) : Set A) = ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left ⁅B, P⁆ P hnormK
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) := by rw [← hmul]; exact hx
  obtain ⟨c, hc, p, hp, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq hc (hnormK hp) (2 ^ k)
  exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩

section Reduction


end Reduction

end CFSG.Quasithin
