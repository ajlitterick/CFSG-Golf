module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Comp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def IsCharTwoLieIndex : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .E6 q | .E7 q | .E8 q
  | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | .reeG2 _ => False

@[expose] def IsChevTwo (Q : Type*) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsCharTwoLieIndex d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)


end CFSG.HardMathSupport.Solomon.Coordinator
