module

public import CFSG.Quasithin.Background.H11MinusField
import CFSG.Quasithin.Background.H11Plus
import CFSG.Quasithin.Background.Harris.L2.OmegaMinusRep
import CFSG.Quasithin.Vol2.Ch6H11Holds
public import CFSG.Quasithin.Vol2.Ch6H11Norm
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H11Proof

open CFSG.Quasithin

section MinusGroup

open scoped Matrix

variable {F : Type} [Field F] [CharP F 2]

private noncomputable abbrev sigQ (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] : AdjoinRoot (quadPoly a) →+* AdjoinRoot (quadPoly a) :=
  iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n


end MinusGroup

section MinusBridge

open scoped Matrix


end MinusBridge

section ModelK


end ModelK

section MinusMain


end MinusMain

section MinusAssembly


end MinusAssembly


end CFSG.Quasithin.H11Proof
