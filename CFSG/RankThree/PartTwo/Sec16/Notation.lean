module

public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type*} [Group G]

@[expose] def scriptY3Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | Maximal (· ∈ scriptY3 A LB) Y}

@[expose] def scriptY1 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY3 A LB ∧ oPrimeResidualOf 3 Y = ⊥}

@[expose] def scriptY1Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | Maximal (· ∈ scriptY1 A LB) Y}

@[expose] def scriptYs (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY1 A LB ∧ Group.IsSolvable Y}


end CFSG.RankThree.PartTwo.Sec16
