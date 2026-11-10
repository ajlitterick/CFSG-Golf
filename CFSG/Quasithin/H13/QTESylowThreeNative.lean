module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.QuasithinUnique.Setup.X1


@[inline, expose] def b64Val (c : UInt8) : Nat :=
  if c.toNat = 43 then 62 else if c.toNat = 47 then 63
  else if c.toNat < 58 then c.toNat - 48 else if c.toNat < 91 then c.toNat - 55
  else c.toNat - 61

@[expose] def b64At (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => b64At b o w * 64 + b64Val (b.get! (o + w))

@[expose] def b64Bit (b : ByteArray) (i : Nat) : Bool :=
  (b64Val (b.get! (i / 6)) >>> (i % 6)) % 2 == 1

structure DecSt where
  Aa : Array Nat
  Ab : Array Nat
  par : Array Nat
  gen : Array Nat
  next : Nat
  k : Nat

@[expose] def decStep (bb tb : ByteArray) (x : Nat) (st : DecSt) (j : Nat) : DecSt :=
  let isTree := b64Bit bb (2 * x + j)
  let y := if isTree then st.next else b64At tb (3 * st.k) 3
  let st1 : DecSt :=
    if isTree then { st with par := st.par.push x, gen := st.gen.push j, next := st.next + 1 }
    else { st with k := st.k + 1 }
  if j = 0 then { st1 with Aa := st1.Aa.push y } else { st1 with Ab := st1.Ab.push y }

@[expose] def decodeAct (N : Nat) (bits tg : String) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  let bb := bits.toUTF8
  let tb := tg.toUTF8
  let st := (List.range N).foldl (fun st x => decStep bb tb x (decStep bb tb x st 0) 1)
    { Aa := #[], Ab := #[], par := #[0], gen := #[0], next := 1, k := 0 }
  (st.Aa, st.Ab, st.par, st.gen)

@[expose] def invArr (n : Nat) (t : Array Nat) : Array Nat :=
  (List.range n).foldl (fun acc i => acc.set! (t.getD i 0) i) (Array.replicate n 0)


end CFSG.Quasithin.H13.QTESylow
