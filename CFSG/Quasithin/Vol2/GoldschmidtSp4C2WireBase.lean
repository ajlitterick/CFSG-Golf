module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PF7
public import CFSG.Quasithin.Vol2.Ch3E213MG41S5
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

theorem factSp4TransvRefl_holds :
    FactSp4TransvRefl :=
  G41.factSp4TransvRefl_of_big G41.Big.factSp4ReflBig_holds

theorem factSp4TransvW_holds :
    FactSp4TransvW :=
  G41.factSp4TransvW_of_refl factSp4TransvRefl_holds

end CFSG.Quasithin.Ch3E213M.Sp4C2
