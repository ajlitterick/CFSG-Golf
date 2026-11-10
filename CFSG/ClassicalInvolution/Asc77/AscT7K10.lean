module

public import CFSG.ClassicalInvolution.Asc77.AscT7K9
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C23_5X_type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (u * e ∈ zStarOf (rLayer Ω u) ∨ LayerOrthType p f Ω u 5 true ∨
        LayerOrthType p f Ω u 6 (!piSign p f))

@[expose] def C23_GammaU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        Subgroup.centralizer ({u} : Set G) ≤
          gamma2 (Subgroup.closure {u * e, u, z}) (Subgroup.centralizer ({u} : Set G))


end CFSG.ClassicalInvolution.Asc77
