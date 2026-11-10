module

public import CFSG.Quasithin.Background.H156Irr
public import CFSG.Quasithin.Background.H153Grp

public section

open scoped Matrix

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H156

abbrev I4 : Type := Fin 2 ⊕ Fin 2


@[expose] def J4 : Matrix I4 I4 (ZMod 2) := Matrix.fromBlocks 0 1 (-1) 0

@[expose] def c4 : List ℕ := [7, 1, 13, 15, 4, 0, 0, 0, 0, 0, 0]


end CFSG.Quasithin.H153
