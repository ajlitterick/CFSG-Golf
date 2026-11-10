module

public import Certificates.Kernel.Trace6091.OddA0
public import CFSG.Certificates.Kernel.Trace6091.ScanRest

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.AxisCount
  CFSG.Monster.Existence Finset

theorem pairA : pairScanT PA (betaTabT PA) = 30 := by decide +kernel

theorem pairA_sum : ∑ q ∈ range 276, (xTerm permMonoA 0 (Model.thetaN 0 ^^^ pairD q) +
    xTerm permMonoA 63 (Model.thetaN 63 ^^^ pairD q)) = 30 :=
  (pairScanT_eq pe_PA).symm.trans pairA


theorem wScanA : wScanT PA (betaTabT PA) = 64 := by decide +kernel

theorem wTrA : wTr (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoA)) = 64 :=
  (wScanT_eq pe_PA).symm.trans wScanA


theorem latTrA : latTr (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoA)) = 6 := by
  rw [latTr_perm]
  decide +kernel

theorem latTr2A : latTr2 (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoA)) = 6 := by
  rw [latTr2_perm]
  decide +kernel


end Certificates.Kernel.Trace6091

end
