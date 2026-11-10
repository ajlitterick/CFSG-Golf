module

public import Certificates.Data.GL33.Code
public import Certificates.Data.GL33.Data

public section

namespace CFSG.GL33.Native

set_option compiler.extract_closed false


@[expose] def evalW (gl : Array Nat) (w : Word) : Nat :=
  w.foldl (fun acc ae => mulF acc (powC gl[ae.1]! ae.2)) oneC


@[expose] def monoC (c : Nat) : Bool :=
  (List.range 3).all fun j => ((List.range 3).filter fun i => ent c i j != 0).length == 1


end CFSG.GL33.Native

end
