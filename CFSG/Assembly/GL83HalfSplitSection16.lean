module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Assembly


@[expose] def LargeEvenSplit16 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (LargeEvenUntwisted lab.tag ∧ p ∣ 2 ^ lab.n - 1) ∨
    (¬ LargeEvenUntwisted lab.tag ∧ lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 ∧
      p ∣ 2 ^ lab.n + 1) ∨
    ((lab.tag = .twD ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) ∧
      p ∣ 2 ^ lab.n - 1) ∨
    (lab.n = 1 ∧ p = 3)

@[expose] def LargeEvenHalfSplit16 (p : ℕ) (lab : LargeEvenLabel)
    (centerTrivial : Prop) : Prop :=
  LargeEvenSplit16 p lab ∨
    ((lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
      p ∣ 2 ^ lab.n + 1) ∨
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (((lab.tag = .A ∧ lab.rank = 5) ∨ lab.tag = .E6) ∧ lab.n = 2 ∧ centerTrivial ∧ p = 5) ∨
    (lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7) ∨
    (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7)


end CFSG.Assembly
