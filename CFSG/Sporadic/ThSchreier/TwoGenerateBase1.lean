
module

public import CFSG.Sporadic.ThSchreier.TwoGenerateBase

public import CFSG.Sporadic.ThSchreier.CentralCentralizerBase1
public import CFSG.Sporadic.ThSchreier.TwoCentralizerBase1
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
public meta import CFSG.Sporadic.ThSchreier.CentralizerData

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 Pointwise

theorem conj_mem_centralizer_a
    {x : J} (hx : x * involT = involT * x) :
    transporterV * x * transporterV⁻¹ ∈ Subgroup.centralizer {a} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : a = transporterV * involT * transporterV⁻¹ := by rw [involT]; group
  rw [e]
  calc transporterV * x * transporterV⁻¹ * (transporterV * involT * transporterV⁻¹) =
        transporterV * (x * involT) * transporterV⁻¹ := by group
    _ = transporterV * (involT * x) * transporterV⁻¹ := by rw [hx]
    _ = _ := by group

section Facts


end Facts

end CFSG.Sporadic.ThSchreier
