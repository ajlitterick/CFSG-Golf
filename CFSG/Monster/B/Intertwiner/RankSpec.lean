module

public import CFSG.Monster.B.Intertwiner.ArithSpec
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.Monster.B

open Bin Matrix


theorem card_lt (n r : ℕ) (hr : r ≤ n) :
    Fintype.card {i : Fin n // (if (i : ℕ) < r then (1 : ZMod 2) else 0) ≠ 0} = r := by
  have : ∀ i : Fin n, ((if (i : ℕ) < r then (1 : ZMod 2) else 0) ≠ 0) ↔ (i : ℕ) < r := by
    intro i; split_ifs with h <;> simp [h]
  simp only [this]
  rw [Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hr]


end CFSG.Monster.B

end
