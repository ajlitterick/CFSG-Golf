module
public import CFSG.Sporadic.HNSchreier.ArchMaskedChecks
public import CFSG.Sporadic.HNSchreier.ArchKernelChunks
public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native

@[expose] def bits32 (n offset : Nat) : Nat := (2^32-1) &&& (n >>> offset)
@[expose] def packedWindow (n start width : Nat) : Nat := (2^width-1) &&& (n >>> start)

theorem bits32_window (n start width offset : Nat) (h : offset+32 ≤ width) :
    bits32 (packedWindow n start width) offset = bits32 n (start+offset) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [bits32, packedWindow, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 32
  · have hw : offset+j < width := by omega
    simp only [hj, hw, decide_true, Bool.true_and, Nat.add_assoc]
  · simp only [hj, decide_false, Bool.false_and]


end CFSG.Sporadic.HNSchreier.Native.Kernel
