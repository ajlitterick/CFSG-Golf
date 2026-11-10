module

public import Certificates.Data.Kernel.D43.Tree

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum

@[expose] noncomputable def aptB (q : Nat) : Bool :=
  bIf(Nat.beq q (nat_lit 0), true, bIf(Nat.beq q (nat_lit 6), true,
    bIf(Nat.beq q (nat_lit 479), true, bIf(Nat.beq q (nat_lit 26571), true,
      bIf(Nat.beq q (nat_lit 15916), true, Nat.beq q (nat_lit 186))))))


@[expose] noncomputable def movesB (F W : Nat → Nat) (j p : Nat) : Bool :=
  strictB (lAp F W j p) fun q => bAnd(Nat.blt q (nat_lit 26572), bIf(Nat.beq q p, false, true))

@[expose] noncomputable def ptChk (F W : Nat → Nat) (p : Nat) : Bool :=
  bIf(aptB p, true, bIf(movesB F W (nat_lit 2) p, true, movesB F W (nat_lit 3) p))

@[expose] noncomputable def ptChunk (F W : Nat → Nat) (c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 256) c)
    (fun p => bIf(Nat.blt p (nat_lit 26572), ptChk F W p, true)) (nat_lit 256)


end CFSG.KC.D43
