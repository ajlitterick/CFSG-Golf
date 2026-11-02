module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Rep4371.ExactActions

public section

namespace CFSG.Sporadic.B

theorem fam_b_simplicity :
    IsSimpleGroup Blueprint.NativeSporadic.B :=
  Monster.B.isSimpleGroup_B_of_rep (V := Monster.B.Vst) Monster.B.Rbasis Monster.B.chi
    (fun k _ t => Monster.B.chi_packetElt_apply k t)

end CFSG.Sporadic.B
