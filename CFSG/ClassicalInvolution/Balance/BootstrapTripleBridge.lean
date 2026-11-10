module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type*} [Group G]

private theorem conj_inv_apply (g x : G) : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
  simp


end CFSG.ClassicalInvolution.Balance.Bootstrap
