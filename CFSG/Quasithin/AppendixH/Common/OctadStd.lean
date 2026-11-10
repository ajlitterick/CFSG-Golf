module

public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open


theorem card_octStab_octad0 :
    Nat.card (octStab octad0) = 322560 :=
  card_octStab isOctad_octad0


end CFSG.ASVolI.AppH
