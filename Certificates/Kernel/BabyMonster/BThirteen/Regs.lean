module

public import Certificates.Kernel.BabyMonster.RegTabMat
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenInputs

public section

namespace CertificateChecks.KernelBM.BThirteen

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

theorem b13_regs : RegsOK (b13Prog ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true
    [31, 32, 44, 45, 46, 81] [BThirteen.X, BThirteen.S, BThirteen.T2, BThirteen.T4, BThirteen.T5,
      BThirteen.G] := by
  bm_reg_cert_mat [CFSG.KC.BM.BThirteen, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.BThirteen

end
