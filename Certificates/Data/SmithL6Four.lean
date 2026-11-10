module

public import Certificates.Data.SmithL6Orbit
public import Std.Data.HashSet

public section

namespace CFSG.SmithL6


@[expose] def isPartner (u : Nat) : Bool := u != 0 && tvImg 0 u == tvImg u 0


@[expose] def fourBase : Nat × Nat × Nat := (1352, 968, 1480)

@[expose] def fourStep (g : Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (tvImg g t.1, tvImg g t.2.1, tvImg g t.2.2)

@[expose] def fourKey (t : Nat × Nat × Nat) : Nat := t.1 + 1953 * (t.2.1 + 1953 * t.2.2)


end CFSG.SmithL6
