module

public import CFSG.Quasithin.AppendixH.H16.TranspAxis
public import CFSG.Quasithin.AppendixH.H16.SextetV10
public import CFSG.Quasithin.AppendixH.H16.SextetData2

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Open

@[expose] noncomputable def ksRho (i : ℕ) : MulAut W11 := rhoCd (ks6_autPerm i)

@[expose] noncomputable def gJ (J : ℕ) : MulAut W11 :=
  (List.range 6).foldl (fun a j => if J.testBit j then a * ksRho j else a) 1


end CFSG.ASVolI.H16
