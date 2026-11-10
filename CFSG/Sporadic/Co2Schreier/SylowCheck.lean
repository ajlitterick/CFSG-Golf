
module


public import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Certificate2059

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.RuSchreier

theorem frat_check : fratCheck fratLevels = true :=
  Certificates.certificate2059.1

theorem profile_check : profileOK fratLevels zArr profTable = true :=
  Certificates.certificate2059.2.1

theorem unique_check : uniqueOK profTable = true :=
  Certificates.certificate2059.2.2

end CFSG.Sporadic.Co2Schreier
