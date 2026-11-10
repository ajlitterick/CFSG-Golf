module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Viol

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def invR (r : Array ℕ) : Array ℕ :=
  ((List.range 12).map fun j =>
    ((List.range 4096).find? fun n => appN r n == 2 ^ j).getD 0).toArray

abbrev St : Type := ℕ × Array ℕ × Array ℕ


@[expose] def withInv (gs : List (Array ℕ)) : List (Array ℕ × Array ℕ) :=
  gs.map fun g => (g, invR g)


@[expose] def okRows (r : Array ℕ) : Bool := r.size == 12 && r.all (· < 4096)


@[expose] def f4Indep (x y : ℕ) : Bool :=
  x != 0 && y != 0 && y != x && y != theta0N x && y != (x ^^^ theta0N x)

@[expose] def f2Indep3 (x y w : ℕ) : Bool :=
  x != 0 && y != 0 && y != x && w != 0 && w != x && w != y && w != (x ^^^ y)


end CFSG.GF2Type.Smith1979.GammaU.Viol
