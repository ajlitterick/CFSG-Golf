module

public import CFSG.LieType.Steinberg.Adjoint.CertE7Weyl
public import CFSG.LieType.Steinberg.Adjoint.CertE7Pairs
public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import CFSG.LieType.Steinberg.Adjoint.CertPinned
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

theorem noG2_E7 : NoG2 .E7 := fun i => Or.inl (by simp [Tag.symmetrizer])

end CFSG.LieType.Steinberg.Adjoint
