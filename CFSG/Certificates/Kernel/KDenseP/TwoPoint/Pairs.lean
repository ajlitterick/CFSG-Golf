
module

public import CFSG.Monster.Existence.TwoPoint.Fi22Check
public import CFSG.Monster.Existence.TwoPoint.HNCheck
public import CFSG.Monster.Existence.TwoPoint.HNTwoBCheck
public import CFSG.Monster.Existence.TwoPoint.ThCheck
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs
public import CFSG.Monster.Existence.TwoPoint.ThreeVCheck
public import CFSG.Monster.Existence.TwoPoint.ThreeVOriginalFalseInputs
public import CFSG.Monster.Existence.TwoPoint.Y433MCheck

public section

namespace CFSG.KC.KDenseP.TwoPoint

open CFSG.Monster.AxisCount CFSG.Monster.Existence
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

abbrev Pairs := List (List Native.Gen × List Native.Gen)

@[expose] def tp3 (eqs nes : Pairs) : Pairs := eqs ++ eqs ++ eqs ++ nes

@[expose] def tauP (l : Pairs) : Pairs := l.map fun e => (e.1 ++ [.tau], e.2 ++ [.tau])

@[expose] def fiRels (idx : List Nat) : Pairs := idx.map fun i => (fiRelW rels[i]!, [])

@[expose] def hnR (idx : List Nat) : Pairs := idx.map fun i => (hnRelW hnRels[i]!, [])

@[expose] def thR (idx : List Nat) : Pairs :=
  idx.map fun i => (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!, [])

@[expose] def yW (j : Nat) : List Native.Gen := fiCAlpha ++ gxProdWord (gxXList j)

@[expose] def bpW : List Native.Gen := fiWAlpha ++ fiWBeta ++ fiWAlpha

@[expose] def gxNode (j : Nat) : Pairs :=
  (if j = 9 then [] else [(yW j ++ fiWAlpha, yW j)]) ++ [(yW j ++ bpW, yW j)]

@[expose] def p6063 : Pairs := [2, 3, 4, 5].flatMap gxNode
@[expose] def p6064 : Pairs := [6, 7, 8].flatMap gxNode
@[expose] def p6065 : Pairs := [9, 10].flatMap gxNode
@[expose] def p6066 : Pairs := [11, 12].flatMap gxNode
@[expose] def p6067 : Pairs := [13, 14].flatMap gxNode
@[expose] def p6068 : Pairs := [15, 16].flatMap gxNode
@[expose] def p6069 : Pairs := [17, 18].flatMap gxNode
@[expose] def p6070 : Pairs := [19, 20].flatMap gxNode
@[expose] def p6071 : Pairs :=
  tauP [(yW 21 ++ fiWAlpha, yW 21)] ++ [(yW 21 ++ bpW, yW 21)] ++ gxNode 22

end CFSG.KC.KDenseP.TwoPoint

end
