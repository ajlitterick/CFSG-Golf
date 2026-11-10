module

public import Certificates.Certificate5023
public import CFSG.GH74.Filter.Sporadic.BMax2

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native


theorem not_gen4_B :
    ¬ Gen4 NativeSporadic.B :=
  not_gen4_B_of_max2

end CFSG.GH74.Filter
