module

public import CFSG.Certificates.Kernel.Trace6091.ScanOdd
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.Existence Finset

@[expose] noncomputable def PA : Nat := nat_lit 111812619503779981116236019230164000

theorem pe_PA : ∀ i < 24, pe PA i = permMonoA[i]! := by decide +kernel

theorem oddA_0 : oddScanT PA (betaTabT PA) 0 256 = 24 := by decide +kernel


end Certificates.Kernel.Trace6091

end
