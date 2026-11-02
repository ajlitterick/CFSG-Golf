module

public import CFSG.LieType.Chevalley.RootOps.Cert.G2
public import CFSG.LieType.Chevalley.RootOps.Cert.F4
public import CFSG.LieType.Chevalley.RootOps.Cert.D4
public import CFSG.LieType.Chevalley.RootOps.Cert.E6
public import CFSG.LieType.Chevalley.RootOps.Cert.E7
public import CFSG.LieType.Chevalley.RootOps.Cert.E8

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem RootOps.dataChecks : ∀ τ : Tag, RootOps.DataChecks τ
  | .G2 => RootOps.dataChecks_G2
  | .F4 => RootOps.dataChecks_F4
  | .D4 => RootOps.dataChecks_D4
  | .E6 => RootOps.dataChecks_E6
  | .E7 => RootOps.dataChecks_E7
  | .E8 => RootOps.dataChecks_E8

@[expose] noncomputable def rootOperatorFamily (τ : Tag) : RootOperatorFamily τ :=
  (RootOps.dataChecks τ).family

end CFSG.LieType.Chevalley
