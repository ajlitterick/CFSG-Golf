module

public import CFSG.Monster.GMS.Facts.DoubleCover
public import CFSG.Monster.GMS.Facts.LeechInvolutions
public import CFSG.Monster.GMS.Facts.LeechOddPairs
public import CFSG.Monster.GMS.Facts.LeechPairs
public import CFSG.Monster.GMS.Facts.TableIV

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

structure GMSInterfaces (d₀ : B) (G : Type) [Group G] : Prop where
  sls : SLSStatement d₀
  tableV : TableVIn G
  leech : LeechStatement
  tableIII : BabyTableIII
  tableIVBaby : BabyTableIV
  threeSwap : DoubleCoverThreeSwapIn G
  leechPair : LeechPairStatement
  leechOddPair : LeechOddPairStatement
  tableIV : TableIVIn G
  leechInv : LeechInvolutionStatement


end CFSG.Monster.GMS
