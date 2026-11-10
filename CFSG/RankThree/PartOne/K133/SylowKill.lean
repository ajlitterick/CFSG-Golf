module

public import CFSG.RankThree.PartOne.K133.TwoLoc

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open scoped Pointwise


theorem not_dvd_card_sylow_of_le_normalizer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (U : Sylow 2 X) (H : Subgroup X) (hH : H ≤ Subgroup.normalizer (U : Set X))
    (hcard : ∀ k : ℕ, p ^ k ∣ Nat.card X → p ^ k ∣ Nat.card H) : ¬ p ∣ Nat.card (Sylow 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  have hidx : Nat.card (Sylow 2 X) = (Subgroup.normalizer (U : Set X)).index :=
    U.card_eq_index_normalizer
  have hN := Subgroup.card_mul_index (Subgroup.normalizer (U : Set X))
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  set v := (Nat.card X).factorization p with hv
  have h1 : p ^ v ∣ Nat.card X := Nat.ordProj_dvd _ _
  have h2 : p ^ v ∣ Nat.card H := hcard v h1
  have h3 : Nat.card H ∣ Nat.card (Subgroup.normalizer (U : Set X)) := Subgroup.card_dvd_of_le hH
  have h4 : p ^ (v + 1) ∣ Nat.card X := by
    rw [← hN, pow_succ]
    exact mul_dvd_mul (h2.trans h3) (hidx ▸ hdvd)
  have h5 := (Nat.Prime.pow_dvd_iff_le_factorization hp hX0).1 h4
  omega

end CFSG.RankThree.PartOne.K133
