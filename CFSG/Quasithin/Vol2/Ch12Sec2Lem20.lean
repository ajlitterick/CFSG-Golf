module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem20

variable {G : Type} [Group G]

theorem normalizer_le_of_hyp1223 [Finite G] (h1226 : Stmt12_2_6) {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h := (h1226 G T L V hH).2 V (Subgroup.normalizer (V : Set G)) hH.irrPlus.2.1 le_rfl le_rfl
  intro x hx
  have hx' : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (V : Set G) := ⟨hx, hx⟩
  rw [← h] at hx'
  exact hx'.2

theorem autOn_le_autOn_inf {U M V : Subgroup G} (hVM : Subgroup.normalizer (V : Set G) ≤ M) :
    autOn U V ≤ autOn (M ⊓ Subgroup.normalizer (V : Set G)) V := by
  unfold autOn
  refine Subgroup.map_mono fun x hx => ?_
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hVM x.2, x.2⟩

theorem four_le_card_of_index_eq_two {V : Subgroup G} [Finite ↥V] (hV2 : IsPGroup 2 ↥V)
    (hV : ¬ Nat.card V ≤ 4) {A : Subgroup ↥V} (hA : A.index = 2) : 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card A * 2 = Nat.card V := by rw [← hA]; exact A.card_mul_index
  obtain ⟨k, hk⟩ := (hV2.to_subgroup A).exists_card_eq
  rw [hk] at hcard ⊢
  rcases k with _ | _ | k
  · exact absurd (by rw [← hcard]; norm_num) hV
  · exact absurd (by rw [← hcard]; norm_num) hV
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Lem20

open Lem20


end CFSG.Quasithin.H13
