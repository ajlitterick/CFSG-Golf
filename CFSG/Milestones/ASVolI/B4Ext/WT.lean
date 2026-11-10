module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.GroupTheory.GLnTwoSplitting Module

section WFix

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


end WFix

section WT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end WT

section WTCard

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}


end WTCard

section WTFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}


end WTFix

section OffBasic

variable {V : Type} [CommGroup V] [Finite V]


end OffBasic

section ElemConv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end ElemConv

end CFSG.ASVolI
