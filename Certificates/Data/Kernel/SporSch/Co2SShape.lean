module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Sporadic.Co2Schreier.WitLit

public section

namespace CFSG.KS.Co2SShape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Co2Schreier
  CFSG.Monster.B.Mathieu

@[expose] noncomputable def mapL {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ ih => List.cons (f x) ih) l


@[expose] noncomputable def rowsK (n b : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (lenL l) n, allL (fun x => Nat.blt x b) l)

@[expose] noncomputable def localShapeK (L : LocalCert) : Bool :=
  bAnd(Nat.beq L.schemaVersion (nat_lit 1),
  bAnd(eqNL L.alignmentOddOrders [nat_lit 3, nat_lit 3],
  bAnd(Nat.beq L.expectedFrattiniRank (nat_lit 5),
  bAnd(eqNL L.expectedCentralizerIndices [nat_lit 56925, nat_lit 1024650],
  bAnd(Nat.beq (lenL L.cInitialWords) (nat_lit 2), bAnd(allL (lettersK (nat_lit 2)) L.cInitialWords,
  bAnd(Nat.beq (lenL L.dWords) (nat_lit 2), bAnd(allL (lettersK (nat_lit 2)) L.dWords,
  bAnd(Nat.beq (lenL L.dStrongDerivations) (nat_lit 5),
  bAnd(wordsL (nat_lit 2) L.dStrongDerivations (nat_lit 0),
  bAnd(Nat.beq (lenL L.rWords) (nat_lit 10), bAnd(allL (lettersK (nat_lit 7)) L.rWords,
  bAnd(lettersK (nat_lit 2) L.cInitialCenterWord, bAnd(lettersK (nat_lit 2) L.dCenterWord,
  bAnd(lettersK (nat_lit 10) L.zRWord, bAnd(lettersK (nat_lit 2) L.alignmentIntermediateWord,
  bAnd(Nat.beq (lenL L.cStrongDerivations) (nat_lit 7),
  bAnd(wordsL (nat_lit 2) L.cStrongDerivations (nat_lit 0),
  bAnd(Nat.beq (lenL L.qWords) (nat_lit 8), bAnd(allL (lettersK (nat_lit 9)) L.qWords,
  bAnd(Nat.beq (lenL L.sQuotientWords) (nat_lit 7),
  bAnd(allL (lettersK (nat_lit 9)) L.sQuotientWords,
  bAnd(Nat.beq (lenL L.frattiniProfiles) (nat_lit 32),
  bAnd(allL (fun p => Nat.beq (lenL p) (nat_lit 12)) L.frattiniProfiles,
  bAnd(chainK L.chains.C (nat_lit 2300) (nat_lit 2) (nat_lit 14)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5],
  bAnd(chainK L.chains.D (nat_lit 2300) (nat_lit 2) (nat_lit 12)
    [nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 3],
  bAnd(chainK L.chains.qAction (nat_lit 512) (nat_lit 2) (nat_lit 17)
    [nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 5, nat_lit 4, nat_lit 7, nat_lit 8, nat_lit 6],
  bAnd(chainK L.chains.rAction (nat_lit 2048) (nat_lit 2) (nat_lit 11)
    [nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 5, nat_lit 8, nat_lit 7, nat_lit 4],
  bAnd(chainK L.chains.S (nat_lit 2300) (nat_lit 15) (nat_lit 23) [nat_lit 0, nat_lit 1, nat_lit 3],
  chainK L.chains.join (nat_lit 2300) (nat_lit 4) (nat_lit 17)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5])))))))))))))))))))))))))))))


end CFSG.KS.Co2SShape

end
