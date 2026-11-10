module

public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.ClassicalInvolution.TwoGroupCase.TwoGroupTI
public import CFSG.ClassicalInvolution.TwoGroupCase.TightPairDihedral
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open
open scoped MatrixGroups

section Tight

variable {G : Type} [Group G]


@[expose] def IsSylowTwoIn (Q M : Subgroup G) : Prop :=
  Q ≤ M ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ (Q.subgroupOf M).index

@[expose] def IsSpecialGroup (W : Subgroup G) : Prop :=
  frattiniOf W = centerOf W ∧ ⁅W, W⁆ = centerOf W


end Tight

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK
open scoped MatrixGroups


section BurnsideIa


end BurnsideIa


section BurnsideIb


namespace burnsideIb_EAData


end burnsideIb_EAData


end BurnsideIb


end CFSG.ASVolI
