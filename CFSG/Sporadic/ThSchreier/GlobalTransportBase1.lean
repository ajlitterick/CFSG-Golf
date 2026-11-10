
module

public import CFSG.Sporadic.ThSchreier.GlobalTransportBase

public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.Th.LocalBase1

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem psiSet_injective : Function.Injective psiSet := Set.image_injective.2 psi_injective

theorem psiSet_smul (g : J) (S : Set V) : psiSet (g • S) = g • psiSet S := psi_image_smul g S

section Facts


end Facts

section Cert


end Cert

end CFSG.Sporadic.ThSchreier
