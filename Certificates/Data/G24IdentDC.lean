module

public import Certificates.Data.G24DCCode

public section

namespace CFSG.Quasithin.St84.G24DC

open CFSG.Fischer CFSG.LieType.Multipliers.G24
open CFSG.Quasithin.St84.G24DC.Code

@[expose] def gB : Array (Array (Array F4)) := (Native.gBN ()).map decMat


@[expose] def wWords : List (List (List (Fin 4))) := Native.wWords


@[expose] def wImg (_ : Unit := ()) : Array (Array (Array (Array F4))) :=
  (Native.wImgN ()).map fun row => row.map decMat


end CFSG.Quasithin.St84.G24DC
