module

public import CFSG.Quasithin.Background.H11Defs
public import CFSG.Quasithin.SteinbergCBTwistedField
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.H11Proof

section MinusField

open Polynomial

variable {F : Type} [Field F]

@[expose] noncomputable def quadPoly (a : F) : F[X] := X ^ 2 + X + C a


end MinusField

section MinusK

open Polynomial


section MinusTheta

open scoped Matrix


end MinusTheta

end MinusK

end CFSG.Quasithin.H11Proof
