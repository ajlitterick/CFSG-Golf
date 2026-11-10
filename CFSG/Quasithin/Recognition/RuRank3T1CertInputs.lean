module

public import CFSG.Quasithin.Recognition.RuRank3T1Data
public import CFSG.Quasithin.H13.QTESylowThreeNative
public import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H13.QTESylow CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def t1Ta : Array Nat := titsDArrs[0]!

@[expose] def t1Tb : Array Nat := titsDArrs[1]!

@[expose] def t1Tai : Array Nat := invArr 1755 t1Ta

@[expose] def t1Tbi : Array Nat := invArr 1755 t1Tb

@[expose] def t1Dec : Array Nat × Array Nat × Array Nat × Array Nat :=
  decodeAct 14976 t1Bits t1Targets


@[expose] def decActPar (d : Array Nat × Array Nat × Array Nat × Array Nat) : Array Nat := d.2.2.1

@[expose] def decActGen (d : Array Nat × Array Nat × Array Nat × Array Nat) : Array Nat := d.2.2.2

@[expose] def t1Par : Array Nat := decActPar t1Dec

@[expose] def t1Gen : Array Nat := decActGen t1Dec

@[expose] def t1NT : Array (Array Nat) := slpTabsA t1Ta t1Tb t1Prog


@[expose] def t1T : Array (Array Nat) := treeTabs 1755 14976 t1Ta t1Tb t1Par t1Gen

@[expose] def t1U : Array (Array Nat) := treeInvTabs 1755 14976 t1Tai t1Tbi t1Par t1Gen


end CFSG.Quasithin.RuRank3
