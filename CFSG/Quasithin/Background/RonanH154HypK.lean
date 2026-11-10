module

public import CFSG.Quasithin.Background.RonanH154Chain
public import CFSG.Quasithin.Background.RonanH154Xor

public section

namespace CFSG.Quasithin.RonanH154.HypK

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.RonanH163 CFSG.KC.Loop


theorem xor32_val (s t : Fin 32) : (RonanH143.xor32 s t).val = s.val ^^^ t.val := by
  have hs : s.val < 2 ^ 5 := s.isLt
  have ht : t.val < 2 ^ 5 := t.isLt
  have h : s.val ^^^ t.val < 2 ^ 5 := Nat.xor_lt_two_pow hs ht
  exact Nat.mod_eq_of_lt h

theorem xor32_self (s : Fin 32) : RonanH143.xor32 s s = 0 :=
  Fin.ext (by rw [xor32_val, Nat.xor_self]; rfl)

theorem xor32_zero (s : Fin 32) : RonanH143.xor32 s 0 = s :=
  Fin.ext (by rw [xor32_val, Fin.val_zero, Nat.xor_zero])

theorem zero_xor32 (s : Fin 32) : RonanH143.xor32 0 s = s :=
  Fin.ext (by rw [xor32_val, Fin.val_zero, Nat.zero_xor])

theorem xor32_comm (s t : Fin 32) : RonanH143.xor32 s t = RonanH143.xor32 t s :=
  Fin.ext (by rw [xor32_val, xor32_val, Nat.xor_comm])

theorem xor32_assoc (s t r : Fin 32) :
    RonanH143.xor32 (RonanH143.xor32 s t) r = RonanH143.xor32 s (RonanH143.xor32 t r) :=
  Fin.ext (by rw [xor32_val, xor32_val, xor32_val, xor32_val, Nat.xor_assoc])

theorem xor32_cancel_left (u v : Fin 32) : RonanH143.xor32 u (RonanH143.xor32 u v) = v := by
  rw [← xor32_assoc, xor32_self, zero_xor32]

theorem xor32_cancel_left' (u v : Fin 32) : RonanH143.xor32 v (RonanH143.xor32 u v) = u := by
  rw [xor32_comm u v, xor32_cancel_left]

theorem xor32_cancel_right (u v : Fin 32) : RonanH143.xor32 (RonanH143.xor32 u v) u = v := by
  rw [xor32_comm, xor32_cancel_left]

theorem xor32_cancel_right' (u v : Fin 32) : RonanH143.xor32 (RonanH143.xor32 u v) v = u := by
  rw [xor32_assoc, xor32_self, xor32_zero]

theorem xor32_closed4 (u v s t : Fin 32) (hs : s = 0 ∨ s = u ∨ s = v ∨ s = RonanH143.xor32 u v)
    (ht : t = 0 ∨ t = u ∨ t = v ∨ t = RonanH143.xor32 u v) :
    RonanH143.xor32 s t = 0 ∨ RonanH143.xor32 s t = u ∨ RonanH143.xor32 s t = v ∨
      RonanH143.xor32 s t = RonanH143.xor32 u v := by
  rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
  all_goals simp only [xor32_self, xor32_zero, zero_xor32, xor32_cancel_left, xor32_cancel_left',
    xor32_cancel_right, xor32_cancel_right', xor32_comm, eq_self_iff_true, true_or, or_true]

end CFSG.Quasithin.RonanH154.HypK
