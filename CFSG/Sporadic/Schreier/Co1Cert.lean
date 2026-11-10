module

public import CFSG.Sporadic.Schreier.Co1CertData
import Certificates.Kernel.Co1B.C2043
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Sporadic.Schreier.Co1StabLift
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.InvariantMerge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD rowsMatrix)
open CFSG.Monster.B.Co2 (permOfArr Rep rep_permOfArr)
open CFSG.Sporadic.Co2Cert (isPermList isPermList_spec rep_of_isPermList co2Q co2P
  co2Q_originalSubgroup)

@[expose] noncomputable def certVec (i : ℕ) : Vec24 := toVecD 24 (co1Rec.vectors.getD i 0)

@[expose] noncomputable def certX : Set Vec24 := {v | ∃ i < 98280, certVec i = v}

end CFSG.Sporadic.Co1Schreier
