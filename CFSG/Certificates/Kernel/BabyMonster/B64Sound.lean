module

public import CFSG.Certificates.Kernel.BabyMonster.B64
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerArith
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM.B64

@[expose] noncomputable def ascC (N len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.blt (chAt N i) (nat_lit 128)) ih) len

@[expose] noncomputable def asciiOK (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun N len => ascC N len) p) ih) L


end CFSG.KC.BM.B64

end

namespace CFSG.KC.BM.B64

open CFSG.KC.YModel CFSG.Monster.B.Bin

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide


def Dq (b : ByteArray) (q : Nat) : Nat :=
  (b64Val (b.get! (4 * q)) <<< 18) ||| (b64Val (b.get! (4 * q + 1)) <<< 12) |||
    (b64Val (b.get! (4 * q + 2)) <<< 6) ||| b64Val (b.get! (4 * q + 3))

def Db (b : ByteArray) (p : Nat) : UInt8 := UInt8.ofNat (Dq b (p / 3) >>> (16 - 8 * (p % 3)))


theorem testBit_mask (n i : Nat) : ((1 <<< n) - 1).testBit i = decide (i < n) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]


end CFSG.KC.BM.B64

public section

namespace CFSG.KC.BM.B64

open CFSG.KC.YModel CFSG.Monster.B.Bin


end CFSG.KC.BM.B64

end
