
module

public import CFSG.Sporadic.ThSchreier.FullAutCoreBase

public import CFSG.Sporadic.ThSchreier.TwoGenerate
public import CFSG.Sporadic.ThSchreier.CoreHyperplane
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public meta import CFSG.Sporadic.ThSchreier.Transporter
public import CFSG.Sporadic.ThSchreier.GlobalIndex
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819
public meta import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.KernelCentralizer
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
