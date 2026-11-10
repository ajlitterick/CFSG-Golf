
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi23Sylow

section Tables

@[expose] noncomputable def qG (j : ℕ) : CFSG.Sporadic.Fi23.J := ((qWords[j]!).map (pairG gs)).prod

theorem qLettersT_nil (L : Array Table) : qLettersT L [] = idT 31671 := by
  unfold qLettersT
  exact List.foldr_nil

theorem qLettersT_cons (L : Array Table) (l : ℕ) (w : List ℕ) :
    qLettersT L (l :: w) = compT 31671 L[l]! (qLettersT L w) := by
  unfold qLettersT
  exact List.foldr_cons

theorem rep_qLettersT : ∀ w : List ℕ, (∀ z ∈ w, z < letters.size) →
    Rep 31671 (qLettersT letters w) (w.map (pairG gs)).prod
  | [], _ => by
    rw [qLettersT_nil, List.map_nil, List.prod_nil]
    exact Rep.idT (by norm_num)
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := rep_qLettersT w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    rw [qLettersT_cons, List.map_cons, List.prod_cons]
    exact (rep_pairG_all l hl).compT ih


theorem eq_of_base {x y : CFSG.Sporadic.Fi23.J} (h : ∀ t < 6, idx 31671 x t = idx 31671 y t) : x = y := by
  have hz : ∀ t < 6, idx 31671 (y⁻¹ * x) t = t := by
    intro t ht
    rw [idx_mul, h t ht, ← idx_mul, inv_mul_cancel, idx_one]
  have hlvl : ∀ i ≤ 6, y⁻¹ * x ∈ lvl i := by
    intro i
    induction i with
    | zero => exact fun _ => mem_lvl_zero _
    | succ i ih =>
      intro hi
      have hbase : CFSG.Sporadic.Fi23.Native.chainBase[i]! = i := by
        have : i < 6 := by omega
        interval_cases i <;> rfl
      refine (chain_facts'.2.1 i (by rw [chainBase_size]; omega) _ (ih (by omega))).1 ?_
      rw [hbase]
      exact hz i (by omega)
  have hcard : Nat.card (lvl 6) = 1 := by
    rw [chain_facts'.2.2 6 (by rw [chainBase_size]), chainBase_size]
    simp
  have h1 : y⁻¹ * x = 1 := by
    have := hlvl 6 le_rfl
    rw [Subgroup.card_eq_one.1 hcard] at this
    exact this
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end Tables

section Enumeration

variable {G : Array Table} {P : Array (ℕ × ℕ)} {img : Array ℕ}
  {N : ℕ}


theorem factorization_three_pow_mul (k m : ℕ) (hm : ¬ 3 ∣ m) :
    (3 ^ k * m).factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]


end Enumeration

section Main

end Main

end Fi23Sylow

open Fi23Sylow

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
