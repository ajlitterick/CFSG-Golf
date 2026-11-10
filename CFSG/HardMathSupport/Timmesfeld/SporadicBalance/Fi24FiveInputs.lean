module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

set_option compiler.extract_closed false


@[expose] def eqTab24 (A B : Table) : Bool := (List.range 306936).all fun i => ap A i == ap B i

@[expose] def fixList24 (W : Table) : List Nat := (List.range 306936).filter fun i => ap W i == i


@[expose] def fiveTab24 (T₀ T₁ : Table) (a b : Nat) : Table :=
  compT 306936 (powT 306936 a T₀) (powT 306936 b T₁)


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
