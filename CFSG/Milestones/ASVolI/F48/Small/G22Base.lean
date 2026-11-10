module

public import CFSG.Quasithin.Recognition.CertU33Outer

public section

namespace CFSG.ASVolI

open CFSG.Quasithin


@[expose] def burnsideF48s_g22Gen (i : Fin 6) : Equiv.Perm (Fin 28) :=
  if h : i.val < 5 then u33Img ⟨i.val, h⟩ else u33Pi


end CFSG.ASVolI
