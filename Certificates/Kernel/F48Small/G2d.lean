module

public import CFSG.Milestones.ASVolI.F48.Small.G2dInputs
public import Certificates.Data.Kernel.F48Small.G2dK
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Kernel.StdOdd.ValsCmd

public section

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.G2dTab CFSG.ASVolI.burnsideF48s_g2dTab

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L CFSG.KC.Ord CFSG.Quasithin

@[expose] noncomputable def ekG2d (w : List (Fin 5 × Bool)) : ℕ :=
  evK 28 (burnsideF48s_g2dGL.map encL) (burnsideF48s_g2dGLi.map encL) w

@[expose] noncomputable def g2dFT (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dTelF k)

@[expose] noncomputable def g2dFTi (k : ℕ) : ℕ :=
  ekG2d (burnsideF48s_invW (burnsideF48s_g2dTelF k))

@[expose] noncomputable def g2dFA (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dAF k)

@[expose] noncomputable def g2dFB (k : ℕ) : ℕ := ekG2d (burnsideF48s_g2dBF k)

@[expose] noncomputable def g2dFV (k : ℕ) : ℕ :=
  ekG2d (u33Word (burnsideF48s_g2dCandV.getD k ""))

@[expose] noncomputable def g2dFW (k : ℕ) : ℕ := ekG2d (u33Word (["Xs", "Y", "X"].getD k ""))

#kc_vals G2dT g2dFT 32
#kc_vals G2dTi g2dFTi 32
#kc_vals G2dA g2dFA 64
#kc_vals G2dA8 g2dFA 8
#kc_vals G2dB g2dFB 64
#kc_vals G2dV g2dFV 4
#kc_vals G2dW g2dFW 3


end CertificateChecks.KernelF48S
