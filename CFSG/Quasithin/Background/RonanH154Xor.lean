module

public import CFSG.Quasithin.Background.RonanH143E2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin.RonanH143

@[expose] def dot5 (h u : ℕ) : Bool :=
  ((h &&& u).testBit 0) ^^ ((h &&& u).testBit 1) ^^ ((h &&& u).testBit 2) ^^
    ((h &&& u).testBit 3) ^^ ((h &&& u).testBit 4)


end CFSG.Quasithin.RonanH154
