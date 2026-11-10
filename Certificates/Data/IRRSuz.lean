module

public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.SylowCheckInputs

public section

namespace CFSG.ComponentClassification.Walter86.IRRSuz

open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native

@[expose] def commT (a b : Tab) : Bool := comp 1782 a b == comp 1782 b a

@[expose] def zWitOK (z b₁ b₂ : Tab) : Bool :=
  commT b₁ z && commT b₂ z && commT b₁ b₂ && !(b₁ == z) && !(b₂ == z) && !(b₂ == b₁) &&
    !(b₂ == comp 1782 z b₁)

@[expose] def witOK (z y zy b : Tab) : Bool :=
  commT b z && commT b y && !(b == y) && !(b == z) && !(b == zy)


end CFSG.ComponentClassification.Walter86.IRRSuz
