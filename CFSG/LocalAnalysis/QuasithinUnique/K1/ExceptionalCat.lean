module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatG2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatRee
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTits
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.QuasithinUnique.K1

theorem k1_exceptional
    (hX : TitsNoStronglyClosedElemAbelian)
    (hA : TitsSylowCentralizingAutInner) : K1FamilyRecognition ExceptionalFamilyCat := by
  intro G _ _ H S U L h hfam w hwU hwS hnc _
  rcases hfam with ⟨f, hg2 | htri | hree | hsz⟩ | htits
  · exact absurd (centralizes_of_g2 h hg2.1 hg2.2 hwU hwS) hnc
  · exact absurd (centralizes_of_triality h htri.1 htri.2 hwU hwS) hnc
  · exact absurd (centralizes_of_ree h hree.2.2 hwU hwS) hnc
  · exact fusionIsBenderGroup_of_suzukiModel hsz.2.2
  · exact absurd (centralizes_of_tits hX hA h htits hwU hwS) hnc

end CFSG.QuasithinUnique.K1
