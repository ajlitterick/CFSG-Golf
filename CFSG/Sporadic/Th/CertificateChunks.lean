module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.Th

open Native

theorem parAll_eq_true_of {n chunks : ℕ} {p : ℕ → Bool} (h : ∀ i < n, p i = true) :
    parAll n chunks p = true := by
  unfold parAll
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply]
  intro j hj
  change allStep j (chunks + 1) n p = true
  unfold allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨k, hk⟩ _
  apply h
  have hcpos : 0 < chunks + 1 := Nat.succ_pos _
  have hle := (Nat.le_div_iff_mul_le hcpos).1 (Nat.succ_le_of_lt hk)
  have e : (k + 1) * (chunks + 1) = (chunks + 1) * k + (chunks + 1) := by ring
  rw [e] at hle
  generalize (chunks + 1) * k = X at hle ⊢
  omega


end CFSG.Sporadic.Th
