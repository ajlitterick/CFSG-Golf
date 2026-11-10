module

public import CFSG.Quasithin.AppendixH.H12.ModelN
public import CFSG.Quasithin.AppendixH.H12.ModelV2
public import CFSG.Quasithin.AppendixH.H12.ModelT0
public import CFSG.Quasithin.AppendixH.H12.Overgroups
public import CFSG.Quasithin.Background.HM22Recog

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsMaximalIn IsExtHatOf ptStab)

abbrev N0 : Subgroup Γ12 := ptStab glHom G0 (ptSub 5)


end CFSG.Quasithin.AppendixH.H12.Model
