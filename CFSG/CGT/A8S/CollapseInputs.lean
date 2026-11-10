module

public import CFSG.CGT.A8S.RelData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable

@[expose] def collRelA8 (k : Fin 7) : A8Word :=
  (5, true) :: nWordA8 ++ (5, true) :: invA8 nWordA8 ++ (5, true) :: invA8 (wrongWordA8 k)

@[expose] def collRelsA8 (k : Fin 7) : List A8Word :=
  relsN0A8.map liftW5 ++ thetaRelsA8 ++ [collRelA8 k]


end CFSG.CGT.A8S
