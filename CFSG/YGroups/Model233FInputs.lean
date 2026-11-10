module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.Model233FData

@[expose] public section

namespace CFSG.YGroups

@[expose] def y233FArrays : Array (Array ℕ) := ModelNative.parsePerms ModelNative.y233FPermText


@[expose] def y233CArrays : Array (Array ℕ) :=
  #[y233FArrays[0]!, y233FArrays[1]!, y233FArrays[3]!, y233FArrays[4]!, y233FArrays[5]!,
    y233FArrays[6]!, y233FArrays[7]!, y233FArrays[8]!]


end CFSG.YGroups
