module

public import Certificates.Kernel.Co2Smith.RootDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

theorem rootPar_k : rootParK = true := by decide +kernel

theorem rootComm_k : rootCommK = true := by decide +kernel

theorem chart_k : chartK = true := by decide +kernel

theorem uOK_k : uOKK = true := by decide +kernel

theorem frame_k : frameK = true := by decide +kernel


end CertificateChecks.KernelCo2Smith
