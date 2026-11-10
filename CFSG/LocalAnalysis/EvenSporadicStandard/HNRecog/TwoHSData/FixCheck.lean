module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native


structure FixData where
  rep : List ℕ
  cent : List (List ℕ)
  centOrder : ℕ
  fix : ℕ
  conjs : List (List ℕ)
  m : ℕ

@[expose] def p0Tabs (ws : List (List ℕ)) : Array Table := (tabsW ws).toArray

@[expose] def p0Invs (ws : List (List ℕ)) : Array Table := (p0Tabs ws).map (invT 1408)

@[expose] def conjTab (c : List ℕ) (x : Table) : Table :=
  conjT 1408 (tabW c) (invT 1408 (tabW c)) x


end CFSG.EvenSporadicStandard.HNRecog
