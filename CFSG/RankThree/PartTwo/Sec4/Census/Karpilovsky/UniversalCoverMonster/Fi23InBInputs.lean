module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.MatrixSeedIdentification
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
  CFSG.Sporadic.Bridge.Fi23GPL.Native

@[expose] def slp : List Instr := [
  .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 7 6, .mu 6 6 2, .mu 5 5 6,
  .mu 5 6 7, .mu 6 7 5, .mu 5 5 6, .mu 6 6 1, .mu 4 4 5, .mu 5 5 6, .mu 6 6 5, .mu 4 5 6,
  .iv 6 7, .mu 7 2 5, .mu 5 6 2, .mu 3 3 4, .mu 3 4 5, .mu 4 5 6, .mu 6 6 5, .iv 5 6,
  .mu 6 1 4, .mu 4 5 1]


@[expose] def wordN (imgs : Array (Array ℕ)) (w : List (ℕ × Bool)) : Array ℕ :=
  w.foldr (fun l acc => (ops2fr 4370).mul imgs[l.1]! acc) (ops2fr 4370).one


end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
