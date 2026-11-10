module

public import CFSG.Milestones.ASVolI.B4Ext.WT

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section Psi

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (φ : V ⧸ U ≃* DualGrp ↥U)


end Psi

section PsiCard

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end PsiCard

end CFSG.ASVolI
