module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def capI : ℕ := 100000

@[expose] def tableI1OK : Bool :=
  let ta := tabW wordA
  let tz := tabW wordZ
  let L := subgroupList capI nWords1
  blkDataOK blkData1 && blkImageOK blkData1 120 && enumW capI 256 nWords1 &&
    nWords1.all (fun w => blkTrivOK blkData1.blk (tabW w)) &&
    nWords1.all (fun w => commTT 1408 (tabW w) tz) && memT 1408 L ta && memT 1408 L tz &&
    sqInOK L (pair4 (idT 1408) ta tz (tabW wordAZ))


@[expose] def tableI3OK : Bool :=
  let tz₁ := tabW wordZ₁
  let LS := subgroupList capI sWords3
  blkDataOK blkData3 && blkImageOK blkData3 60 && enumW capI 960 sWords3 &&
    sWords3.all (fun w => commTT 1408 (tabW w) tz₁) && enumW capI 16 nWords3 &&
    nWords3.all (fun w => blkTrivOK blkData3.blk (tabW w)) &&
    nWords3.all (fun w => memT 1408 LS (tabW w)) &&
    sqOneOK (idT 1408) (subgroupList capI nWords3) && !memT 1408 LS (tabW wordA) &&
    !memT 1408 LS tz₁ && !memT 1408 LS (tabW (wordA ++ wordZ₁))


end CFSG.EvenSporadicStandard.HNRecog
