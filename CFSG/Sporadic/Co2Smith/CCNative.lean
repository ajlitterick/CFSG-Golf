module

public import Certificates.Data.CFSGNative.Co2Smith.Census

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false


@[expose] def conjC (g gi y : Array Nat) : Array Nat := mulRowsF (mulRowsF g y) gi


@[expose] def ccReps : List (Nat × Nat) :=
  [(1, 0), (0, 26805), (32, 26805), (0, 2331), (2, 2331), (80, 2331), (0, 1082), (13, 1082),
    (0, 144)]

@[expose] def ccSqZ : List Nat := [1792, 0, 0, 384, 192, 384, 0, 0, 0]

@[expose] def ccSqR : List Nat := [5376, 0, 0, 1152, 128, 384, 512, 0, 0]

@[expose] def ccCls : List Nat := [270, 1008, 1008, 1260, 22680, 1260, 15120, 15120, 120960]

@[expose] def ccCE : List Nat := [256, 32, 32, 128, 64, 128, 32, 32, 16]

@[expose] def ccInvE : List Nat := [272, 32, 32, 80, 80, 80, 32, 32, 32]


@[expose] def ccSylSize : List Nat := [65536, 32768, 65536]

end CFSG.Sporadic.Co2Smith.Native
