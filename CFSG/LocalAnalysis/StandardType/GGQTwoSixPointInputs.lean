module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointRels
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableIndexGe
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable

@[expose] def chart5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15]

@[expose] def chart4 : List ℕ := [0, 1, 2, 3, 4, 5, 8, 9, 10, 11]

@[expose] def rels5 (_ : Unit := ()) : List (List (Fin 14 × Bool)) :=
  restrictWords (subsetOf 18 chart5) relsP

@[expose] def rels4 (_ : Unit := ()) : List (List (Fin 10 × Bool)) :=
  restrictWords (subsetOf 14 chart4) (rels5 ())


end CFSG.StandardType.QTwo.SixPoint

end
