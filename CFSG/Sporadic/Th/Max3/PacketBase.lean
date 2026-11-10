
module

public import CFSG.Sporadic.Th.Max3.CoreBase
public import CFSG.Sporadic.Th.Max3.PacketInputs
public meta import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.Th.Max3.RelationsBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.Certificates

namespace Packet

inductive Instr : Type
  | mu (i j k : ℕ) : Instr
  | iv (i k : ℕ) : Instr
  | pwr (e i k : ℕ) : Instr


@[expose] def Instr.target : Instr → ℕ
  | .mu _ _ k => k
  | .iv _ k => k
  | .pwr _ _ k => k


end Packet

namespace Packet

end Packet

namespace Packet

end Packet

namespace Packet

@[expose] def bits (k : Fin 512) : Fin 9 → ZMod 2 := fun i => ((k.val / 2 ^ i.val : ℕ) : ZMod 2)

theorem bits_val (k : Fin 512) (i : Fin 9) : (bits k i).val = k.val / 2 ^ i.val % 2 := by
  simp [bits, ZMod.val_natCast]

theorem bits_sum (k : Fin 512) : ∑ i : Fin 9, (bits k i).val * 2 ^ i.val = k.val := by
  simp only [bits_val]
  revert k
  decide +kernel

theorem bits_injective : Function.Injective bits := by
  intro k l h
  apply Fin.ext
  rw [← bits_sum k, ← bits_sum l, h]

theorem bits_surjective : Function.Surjective bits := by
  have h : Function.Bijective bits := by
    refine bits_injective.bijective_of_nat_card_le ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, Nat.card_fin]
    norm_num
  exact h.2

end Packet

namespace Packet

private theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn R _ _ fun i => h i.succ)

theorem B1_mul_B1 : B1 * B1 = 1 := by decide

end Packet

end CFSG.Sporadic.Th.Max3
