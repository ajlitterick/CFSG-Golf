module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedTorus
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

@[expose] def DeltaEdgeless (K : Subgroup G) : Prop := ∀ X Y, ¬ commutingAdj K X Y


end CFSG.ClassicalInvolution.Disconnected
