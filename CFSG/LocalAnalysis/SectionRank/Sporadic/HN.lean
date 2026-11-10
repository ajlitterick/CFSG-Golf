module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.SectionRank.HN
public meta import Certificates.Data.CFSGNative.SectionRank.HN
public import Certificates.Certificate8017

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem HN_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.HN, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8017

end CFSG.SectionRank
