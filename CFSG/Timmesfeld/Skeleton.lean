module

public import CFSG.Timmesfeld.Reduction.RootClass
public import CFSG.Timmesfeld.Final.Conclusion

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open


@[expose] def ARSInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), ARS.Hyp G R → Outcome G


end CFSG.Timmesfeld
