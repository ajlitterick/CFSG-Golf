module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectMA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LayerLieType {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  SectionLieType p f (exactFamily Ω c) (exactLayer Ω c) t n

@[expose] def LayerOrthType {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G)
    (d : ℕ) (ε : Bool) : Prop :=
  SectionOrthType p f (exactFamily Ω c) (exactLayer Ω c) d ε


section Compare


end Compare

end CFSG.ClassicalInvolution.Asc77
