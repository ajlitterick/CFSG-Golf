module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB

public section

namespace CFSG.YGroups.DCE.B

@[expose] def letterTok (c : Nat) : Nat := 2 ^ 62 + c

@[expose] def tokens (b : ByteArray) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (b.size / 3)
  let mut cur : Nat := 0
  let mut inNum := false
  for c in b do
    if 48 ≤ c.toNat && c.toNat ≤ 57 then
      cur := cur * 10 + (c.toNat - 48)
      inNum := true
    else
      if inNum then
        out := out.push cur
        cur := 0
        inNum := false
      if 65 ≤ c.toNat && c.toNat ≤ 90 then out := out.push (letterTok c.toNat)
  if inNum then out := out.push cur
  return out


structure Cert where
  prog : Array Ins
  words : Array (Nat × Array Nat)
  fins : Array (Nat × NodeFin)

@[inline, expose] def take (t : Array Nat) (i k : Nat) : Array Nat := t.extract i (i + k)


end CFSG.YGroups.DCE.B
