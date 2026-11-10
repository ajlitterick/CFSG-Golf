module

public import CFSG.LieType.Steinberg.Adjoint.CertE6Weyl
public import CFSG.LieType.Steinberg.Adjoint.CertE6Pairs
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

theorem noG2_E6 : NoG2 .E6 := fun i => Or.inl (by simp [Tag.symmetrizer])

end CFSG.LieType.Steinberg.Adjoint
