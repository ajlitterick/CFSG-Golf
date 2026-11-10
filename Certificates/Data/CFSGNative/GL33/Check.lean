module

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def N : Nat := 19683


@[expose] def act (T : Array Nat) (c r : Nat) : Nat := T[r * 19683 + c]!

@[expose] def mulc (T : Array Nat) (a b : Nat) : Nat :=
  act T b (a % 27) + 27 * act T b ((a / 27) % 27) + 729 * act T b ((a / 729) % 27)


@[expose] def negV (r : Nat) : Nat :=
  (2 * (r % 3)) % 3 + 3 * ((2 * ((r / 3) % 3)) % 3) + 9 * ((2 * ((r / 9) % 3)) % 3)


end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
