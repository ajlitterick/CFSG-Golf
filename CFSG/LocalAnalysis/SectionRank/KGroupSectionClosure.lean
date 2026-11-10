module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Foundations.Catalog

public section

namespace CFSG.SectionRank


theorem K_group_section_closure_inCatalog {X Y : Type} [Group X] [Group Y]
    (hX : CFSG.IsKGroup X) (H : Subgroup X) (N : Subgroup H) [N.Normal] (f : H ⧸ N ≃* Y) :
    CFSG.IsKGroup Y :=
  ((hX.subgroup H).quotient N).of_mulEquiv f.symm

end CFSG.SectionRank
