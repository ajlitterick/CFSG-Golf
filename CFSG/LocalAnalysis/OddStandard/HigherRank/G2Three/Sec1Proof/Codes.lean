module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCodes
public import Mathlib.Tactic.Basify

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

abbrev Wm : Type := Matrix (Fin 14 ⊕ Fin 14) (Fin 14 ⊕ Fin 14) (ZMod 3)

@[expose] def wdiag (A B : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Wm := Matrix.fromBlocks A 0 0 B

@[expose] def wanti (A B : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Wm := Matrix.fromBlocks 0 A B 0

theorem wdiag_mul (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wdiag A B * wdiag C D = wdiag (A * C) (B * D) := by
  simp [wdiag, Matrix.fromBlocks_multiply]

theorem wdiag_mul_wanti (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wdiag A B * wanti C D = wanti (A * C) (B * D) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wanti_mul_wdiag (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wanti A B * wdiag C D = wanti (A * D) (B * C) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wanti_mul_wanti (A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wanti A B * wanti C D = wdiag (A * D) (B * C) := by
  simp [wdiag, wanti, Matrix.fromBlocks_multiply]

theorem wdiag_one : wdiag 1 1 = (1 : Wm) := Matrix.fromBlocks_one

@[expose] def pcFlag (c : List ℕ) : Bool := c.headD 0 == 1

@[expose] def pcA (c : List ℕ) : List ℕ := (c.drop 1).take 196

@[expose] def pcB (c : List ℕ) : List ℕ := (c.drop 197).take 196

@[expose] def mkPc (f : Bool) (a b : List ℕ) : List ℕ := (if f then 1 else 0) :: (a ++ b)

@[expose] def decPc (c : List ℕ) : Wm :=
  if pcFlag c then wanti (dec14 (pcA c)) (dec14 (pcB c)) else wdiag (dec14 (pcA c)) (dec14 (pcB c))


@[expose] def canonPc (c : List ℕ) : Bool :=
  c.length == 393 && (c.headD 0 == 0 || c.headD 0 == 1) && canon14 (pcA c) && canon14 (pcB c) &&
    (pcA c).any fun t => t != 0


theorem pcFlag_mkPc (f : Bool) (a b : List ℕ) : pcFlag (mkPc f a b) = f := by
  cases f <;> simp [pcFlag, mkPc]

theorem pcA_mkPc (f : Bool) {a : List ℕ} (b : List ℕ) (ha : a.length = 196) :
    pcA (mkPc f a b) = a := by
  simp [pcA, mkPc, List.take_left' ha]

theorem pcB_mkPc (f : Bool) {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    pcB (mkPc f a b) = b := by
  simp [pcB, mkPc, List.drop_left' ha, List.take_of_length_le hb.le]

theorem length_one14 : one14.length = 196 := by simp [one14]

theorem decPc_mkPc_false {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    decPc (mkPc false a b) = wdiag (dec14 a) (dec14 b) := by
  unfold decPc
  rw [pcFlag_mkPc, pcA_mkPc _ _ ha, pcB_mkPc _ ha hb]
  simp

theorem decPc_mkPc_true {a b : List ℕ} (ha : a.length = 196) (hb : b.length = 196) :
    decPc (mkPc true a b) = wanti (dec14 a) (dec14 b) := by
  unfold decPc
  rw [pcFlag_mkPc, pcA_mkPc _ _ ha, pcB_mkPc _ ha hb]
  simp


theorem canonPc_spec {c : List ℕ} (h : canonPc c = true) :
    c.length = 393 ∧ (c.headD 0 = 0 ∨ c.headD 0 = 1) ∧ canon14 (pcA c) = true ∧
      canon14 (pcB c) = true ∧ (pcA c).any (fun t => t != 0) = true := by
  simp only [canonPc, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
