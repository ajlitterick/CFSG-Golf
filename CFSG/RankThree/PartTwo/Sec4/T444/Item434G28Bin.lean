module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin

@[expose] def bz (b : Bool) : GF8 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def row2 (a i : ℕ) : ℕ := (a >>> (6 * i)) % 64


@[expose] def comb2 (r b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (if r.testBit m then row2 b m else 0) ^^^ comb2 r b m


@[expose] def mul2Go (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (comb2 (row2 a m) b 6 <<< (6 * m)) ||| mul2Go a b m


@[expose] def mul2 (a b : ℕ) : ℕ := mul2Go a b 6


@[expose] def dec2 (a : ℕ) : Matrix (Fin 6) (Fin 6) GF8 :=
  Matrix.of fun i j => bz (a.testBit (6 * i.val + j.val))


@[expose] def id2 : ℕ := 34630287489

theorem id2_lt : id2 < 2 ^ 36 := by norm_num [id2]

theorem dec2_id2 : dec2 id2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

@[expose] def pw2 (a : ℕ) : ℕ → ℕ
  | 0 => id2
  | k + 1 => mul2 (pw2 a k) a


theorem dec2_injective {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : dec2 a = dec2 b) :
    a = b := by
  refine Nat.eq_of_testBit_eq fun n => ?_
  by_cases hn : n < 36
  · have hi : n / 6 < 6 := by omega
    have hj : n % 6 < 6 := by omega
    have := congrFun (congrFun h ⟨n / 6, hi⟩) ⟨n % 6, hj⟩
    simp only [dec2, Matrix.of_apply] at this
    have e : 6 * (n / 6) + n % 6 = n := by omega
    rw [e] at this
    exact bz_injective this
  · have h36 : 2 ^ 36 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le h36), Nat.testBit_eq_false_of_lt (hb.trans_le h36)]


@[expose] def letterBin (n g : ℕ) : Bool :=
  (List.range 36).all fun t => (letterCode n)[t]! == (if g.testBit t then 1 else 0)

theorem decode_letterCode_eq_dec2 {n g : ℕ} (h : letterBin n g = true) :
    decode (letterCode n) = dec2 g := by
  ext i j
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have h1 : (letterCode n)[6 * i.val + j.val]! =
      if g.testBit (6 * i.val + j.val) then 1 else 0 := by
    have h' := h
    simp only [letterBin, List.all_eq_true, List.mem_range, beq_iff_eq] at h'
    exact h' _ ht
  simp only [decode, dec2, Matrix.of_apply, h1, bz]
  split_ifs <;> rfl

end CFSG.RankThree.PartTwo.Sec4.Item434G28
