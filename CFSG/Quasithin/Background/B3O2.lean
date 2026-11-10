module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.B3Basic

public section

namespace CFSG.Quasithin.B3

@[expose] def O2s {G : Type*} [Group G] (X : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 ↥X).map X.subtype


end CFSG.Quasithin.B3
