
module

public import CFSG.Sporadic.Co1Block.TwoBCentBase

public import CFSG.Sporadic.Co1Block.TwoBExtraCheck
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.FormsBase1
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix

theorem conjB_parts :
    (Native.dag [Native.aR, Native.bR] conjBDerivs).2.2 = true ∧
    Native.mul (conjBRows.getD 10 Native.one) Native.aR =
      Native.mul CFSG.Sporadic.Co1.Module.rowsSB (conjBRows.getD 10 Native.one) := by
  have h := conjB_check
  simp only [conjBCheckOf, List.getD_cons_zero, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem rep_conjB :
    MRep (conjBRows.getD 10 Native.one) conjB :=
  getD_rep (dag_rep (.cons rep_A₁ (.cons rep_A₂ .nil)) conjBDerivs conjB_parts.1) MRep.one 10

end CFSG.Sporadic.Co1Block
