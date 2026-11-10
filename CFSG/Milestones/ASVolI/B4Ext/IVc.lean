module

public import CFSG.Milestones.ASVolI.B4Ext.IVb
public import CFSG.Milestones.ASVolI.B4Ext.Parab

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section PreWCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end PreWCore

section PsiBij

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}


end PsiBij

section StabCorr

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (φ : V ⧸ U ≃* DualGrp ↥U)


end StabCorr

section Rad

variable {V : Type} [CommGroup V]


end Rad

section FiveClass

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end FiveClass

end CFSG.ASVolI
