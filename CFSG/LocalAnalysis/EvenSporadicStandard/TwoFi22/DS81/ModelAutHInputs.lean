module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

@[expose] def autHText : String :=
  include_str "../../../../../Certificates/Data/CFSGNative/FischerOddCore/fi22-aut-h.txt"

@[expose] def autHBytes : ByteArray := autHText.toUTF8

@[expose] def autHDigit (c : UInt8) : ℕ := if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

@[expose] def autHLine (L : ℕ) : Array ℕ :=
  Array.ofFn (n := 3510) fun i =>
    let o := L * (3 * 3510 + 1) + 3 * i.val
    autHDigit (autHBytes.get! o) * 256 + autHDigit (autHBytes.get! (o + 1)) * 16 +
      autHDigit (autHBytes.get! (o + 2))

@[expose] def autHBasis : Array (Array ℕ) := Array.ofFn (n := 10) fun i => autHLine i.val

@[expose] def autHMasks : List ℕ :=
  ((autHText.splitOn "\n")[10]!.splitOn " ").map String.toNat!

@[expose] def autHWord (L : ℕ) : List ℕ :=
  (autHText.splitOn "\n")[L]!.toList.map fun c => c.toNat - 48

@[expose] def autHZ : Array ℕ := (fi22OuterStrong3510 1)[0]!


end CFSG.EvenSporadicStandard.TwoFi22.DS81
