module

public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem exists_big_elem_abelian {Ω : Type} [Group Ω] [Finite Ω] {S E₀ : Subgroup Ω} {x : Ω}
    (hE₀S : E₀ ≤ S) (hE₀ : IsElemAbelian 3 E₀) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxc : ∀ g : Ω, g * x = x * g)
    (hE : 3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) ≤ Nat.card E₀) :
    ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ S ⊔ Subgroup.zpowers x ∧ 3 ^ 5 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxz : x ∈ Subgroup.center Ω := Subgroup.mem_center_iff.2 hxc
  have hCz : Subgroup.zpowers x ≤ Subgroup.center Ω := Subgroup.zpowers_le.2 hxz
  have hCN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set Ω) :=
    hCz.trans (Subgroup.center_le_normalizer _)
  have hCS : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) :=
    hCz.trans (Subgroup.center_le_centralizer _)
  have hC3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a _ b hb =>
    (Subgroup.mem_center_iff.1 (hCz hb) a)
  refine ⟨E₀ ⊔ Subgroup.zpowers x,
    IsElemAbelian.sup_of_commute hE₀ (isElemAbelian_zpowers hx3) hcomm,
    sup_le_sup_right hE₀S _, ?_⟩
  have h2 := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hC3] at h2
  have h3 : Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E₀ hCS)
  have hz : 0 < Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := Nat.card_pos
  have h4 : 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
    calc 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)
        = 3 * (3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)) := by ring
      _ ≤ 3 * (3 ^ 4 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ 3 * Nat.card E₀ := Nat.mul_le_mul_left _ hE
      _ = Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
        rw [h2, mul_comm]
  exact Nat.le_of_mul_le_mul_right h4 hz


end CFSG.LocalAnalysis.GLTheoremA.S265D

end
