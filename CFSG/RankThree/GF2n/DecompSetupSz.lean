module

public import CFSG.RankThree.GF2n.DecompSetupNat

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender Matrix
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace DecompSetup

variable {A Ab L Lb M : Subgroup G} (S : DecompSetup A Ab L Lb M)
include S

section Quot

variable [(M.subgroupOf (A ⊔ Ab)).Normal]

local notation "πm" => QuotientGroup.mk' (Subgroup.subgroupOf M (A ⊔ Ab))

variable (P : QuotPair ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
  ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))))
include P

end Quot

end DecompSetup

end CFSG.RankThree.GF2n
