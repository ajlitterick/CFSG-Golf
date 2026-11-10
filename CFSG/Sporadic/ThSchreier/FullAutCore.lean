
module

public import CFSG.Sporadic.ThSchreier.FullAutCoreBase

public import CFSG.Sporadic.ThSchreier.TwoGenerate
public import CFSG.Sporadic.ThSchreier.CoreHyperplane
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public meta import CFSG.Sporadic.ThSchreier.Transporter
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819
public meta import CFSG.Sporadic.Th.Max3.Packet
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.Rigidity
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.KernelSimple

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms

theorem twoR_mem_M :
    twoR ∈ M := Q_le_M twoR_mem_Q

theorem twoR_not_mem_center :
    (⟨twoR, twoR_mem_Q⟩ : Q) ∉ Subgroup.center Q := by
  rw [center_Q, Subgroup.mem_subgroupOf]
  exact twoR_not_mem_zpowers


end CFSG.Sporadic.ThSchreier
