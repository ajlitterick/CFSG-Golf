module

import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG Subgroup

theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}
    (_hp : 1 < p) (e : X ≃* Y) : pRank p X = pRank p Y := CFSG.pRank_congr_of_mulEquiv e p


end CFSG.ComponentClassification.UnbalancedLayer
