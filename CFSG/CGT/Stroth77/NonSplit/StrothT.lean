module

public import Certificates.Certificate778702

public section

namespace CFSG.CGT.Stroth77

open Equiv Equiv.Perm

theorem Eg_eq_Qns : Eg = Qns :=
  Certificates.certificate778702.2.2.2.1

theorem card_Eg : Nat.card Eg = 16 := by rw [Eg_eq_Qns, card_Qns]

theorem card_Tg : Nat.card Tg = 256 :=
  Certificates.certificate778702.2.2.2.2.1

theorem card_Ag : Nat.card Ag = 32 :=
  Certificates.certificate778702.2.2.2.2.2.1

theorem mem_Ag {g : Mns} : g ∈ Ag ↔ g ∈ bfsList gensA 60 :=
  Certificates.certificate778702.2.2.2.2.2.2.2.1 g


theorem gensA_sub : ∀ g ∈ gensA, g ∈ gensT := by
  simp [gensA, gensT]

theorem Ag_le_Tg : Ag ≤ Tg := by
  rw [Ag, Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (gensA_sub g hg)

theorem Tg_isSylow : ∃ S : Sylow 2 Mns, (S : Subgroup Mns) = Tg := by
  refine ⟨Sylow.ofCard Tg ?_, rfl⟩
  rw [card_Tg, card_Mns]
  rw [show (11520 : ℕ) = 2 ^ 8 * 45 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num


theorem Ag_sup_Lg : Ag ⊔ Lg = NAg :=
  Certificates.certificate778702.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Lg_le_normalizer : Lg ≤ NAg := by
  rw [← Ag_sup_Lg]
  exact le_sup_right


end CFSG.CGT.Stroth77
