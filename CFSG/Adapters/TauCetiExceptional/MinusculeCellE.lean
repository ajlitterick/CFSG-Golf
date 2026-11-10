module

public import CFSG.Adapters.TauCetiExceptional.MinusculeCore
public import CFSG.Adapters.TauCetiExceptional.MinusculeClosure

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.BigCell TauCeti

theorem e6Data_degOrdered : DegOrdered e6Data := by
  unfold DegOrdered
  decide +kernel

theorem e7Data_degOrdered : DegOrdered e7Data := by
  unfold DegOrdered
  decide +kernel


end CFSG.TauCetiBridge.Minuscule
