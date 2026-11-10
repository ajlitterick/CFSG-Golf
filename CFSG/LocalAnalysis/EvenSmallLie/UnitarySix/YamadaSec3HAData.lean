module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)

@[expose] def dArr : Array (Array ℕ) := #[idA 693, dTab, d2Tab, sTab, dsTab, d2sTab]

@[expose] def gz : Array ℕ := gA 14

@[expose] def chX3A3 : ChainData where
  gens := [[4], [2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-2, 7], [-6, 11], [-3, 12], [-1, -3, 6, 1], [-10, -15, -13, 8, 1]]
  base := [45, 3, 1]

@[expose] def chSigA3 : ChainData where
  gens := [[4], [17], [2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-3, 8], [-7, 12], [-4, 13], [-1, -4, 7, 1], [-11, -16, -14, 9, 1],
    [-16, 18, -10, 6, 2]]
  base := [45, 3, 1]

@[expose] def lvX3A3 : Array Level := chX3A3.levels


@[expose] def c10Wit (k d : Array ℕ) : Bool :=
  chA1.O.any fun g => !(allLt 693 fun p =>
    let r := g[k[d[p]!]!]!
    let l := k[d[g[p]!]!]!
    l == r || l == gz[r]!)


@[expose] def fixCnt (a : Array ℕ) : ℕ := (List.range 693).countP fun p => a[p]! == p


@[expose] def lsGens : Array (Array ℕ) := chLam.O ++ chSig.O


@[expose] def nmCheck : Bool :=
  chP2.O.all (validA 693) &&
  (chA1.O.all fun a => chZ2S.O.all fun g => siftA 693 lvZ2S chZ2S.B 0 (conjA 693 a g)) &&
    (chA1.O.all fun a => chA4.O.all fun g => siftA 693 lvA4 chA4.B 0 (conjA 693 a g)) &&
    (chP2.O.all fun a => chA4.O.all fun g => siftA 693 lvA4 chA4.B 0 (conjA 693 a g))

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
