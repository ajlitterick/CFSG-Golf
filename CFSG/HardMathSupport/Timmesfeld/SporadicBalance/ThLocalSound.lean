module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal

open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)
open CFSG.Assembly (IsElemAbelian)


section Table

variable {W : Type*} [Group W] {p : ℕ → W} {m N : ℕ} {g : ℕ → W} {edges : Array (Array ℕ)}
  {par lab : Array ℕ}


@[expose] def QConj (Q : Subgroup W) (x y : W) : Prop := ∃ q ∈ Q, x = q * y * q⁻¹

theorem QConj.refl (Q : Subgroup W) (x : W) : QConj Q x x := ⟨1, Q.one_mem, by group⟩


end Table


section Pair

variable {G : Type*} [Group G]

theorem pow_eq_pow_mod_three {x : G} (hx : x ^ 3 = 1) (n : ℕ) : x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def pairProd (x y : G) (ij : Fin 3 × Fin 3) : G := x ^ ij.1.val * y ^ ij.2.val

theorem pairProd_mul {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (u v : Fin 3 × Fin 3) :
    pairProd x y u * pairProd x y v = pairProd x y
      (⟨(u.1.val + v.1.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨(u.2.val + v.2.val) % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  unfold pairProd
  rw [← pow_eq_pow_mod_three hx, ← pow_eq_pow_mod_three hy, pow_add, pow_add]
  have hc : y ^ u.2.val * x ^ v.1.val = x ^ v.1.val * y ^ u.2.val :=
    ((hxy.pow_pow v.1.val u.2.val).eq).symm
  calc x ^ u.1.val * y ^ u.2.val * (x ^ v.1.val * y ^ v.2.val)
      = x ^ u.1.val * (y ^ u.2.val * x ^ v.1.val) * y ^ v.2.val := by group
    _ = x ^ u.1.val * (x ^ v.1.val * y ^ u.2.val) * y ^ v.2.val := by rw [hc]
    _ = x ^ u.1.val * x ^ v.1.val * (y ^ u.2.val * y ^ v.2.val) := by group


@[expose] def pairSubgroup {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    Subgroup G where
  carrier := Set.range (pairProd x y)
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨_, (pairProd_mul hxy hx hy u v).symm⟩
  one_mem' := ⟨(0, 0), by simp [pairProd]⟩
  inv_mem' := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine ⟨(⟨(3 - i.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(3 - j.val) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [pairProd_mul hxy hx hy]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : (i.val + (3 - i.val) % 3) % 3 = 0 := by omega
    have h2 : (j.val + (3 - j.val) % 3) % 3 = 0 := by omega
    simp only [pairProd, h1, h2, pow_zero, mul_one]

theorem closure_pair_eq_range {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    (Subgroup.closure ({x, y} : Set G) : Set G) = Set.range (pairProd x y) := by
  apply le_antisymm
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ pairSubgroup hxy hx hy := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact ⟨(1, 0), by simp [pairProd]⟩
      · exact ⟨(0, 1), by simp [pairProd]⟩
    exact fun v hv => hle hv
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    have hx' : x ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert x _)
    have hy' : y ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
    show x ^ i.val * y ^ j.val ∈ Subgroup.closure ({x, y} : Set G)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx' _) (Subgroup.pow_mem _ hy' _)

theorem card_closure_pair {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hinj : Function.Injective (pairProd x y)) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
  have e : Nat.card (Subgroup.closure ({x, y} : Set G)) = Nat.card (Set.range (pairProd x y)) := by
    rw [← closure_pair_eq_range hxy hx hy, SetLike.coe_sort_coe]
  rw [e, Nat.card_range_of_injective hinj]
  simp

theorem isElemAbelian_closure_pair {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure ({x, y} : Set G)) := by
  refine isElemAbelian_closure_of_comm ?_ ?_
  · intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  · intro u hu
    rcases hu with rfl | rfl
    · exact hx
    · exact hy

end Pair

section Main


theorem factorization_J :
    (Nat.card CFSG.Sporadic.Th.J).factorization 3 = 10 := by
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 3 ^ 10 * 1536790528000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl


end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
