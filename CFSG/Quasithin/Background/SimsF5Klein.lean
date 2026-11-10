module

public import CFSG.Quasithin.Background.SimsF5Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.Quasithin.H13.ModelsLinear

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open scoped Matrix
open CFSG.Open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatLeafProof.KleinSix
  (rhoGL rhoGL_apply transv range_eq_elementaryGroup coordsOf coordsOf_skewOf skewOf)


end

end CFSG.Quasithin.SimsF5
