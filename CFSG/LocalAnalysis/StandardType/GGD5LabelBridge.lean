module

public import CFSG.LocalAnalysis.StandardType.GGD5Inputs
import CFSG.LocalAnalysis.StandardType.GGD5LabelL
import CFSG.LocalAnalysis.StandardType.GGD5LabelJ
import CFSG.LocalAnalysis.StandardType.GGD5LabelAJ
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggD5LabelDataInput_holds :
    GGD5LabelDataInput := by
  intro G _ _ p B Bs x L D J hS hp _ hxL _ y K hnb M e hecart he0 hb2 _ hbas
  have hD4 := lup10d_label_L hS hp hxL M e hecart he0 hbas
  obtain ⟨hlabJ, hJaut⟩ := lup10d_omegaEnd hS hp M e hbas hD4
  have hcore := lup10d_labelCore_of_labelJ hS hp hlabJ
  exact ⟨hcore.1, hcore.2.1,
    lup10d_labelAJ_of_fix hS hp hnb M e hecart he0 hb2 hbas hJaut, hcore.2.2⟩

end CFSG.StandardType

end
