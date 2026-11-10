module

public import CFSG.Quasithin.Vol2.Ch11SecWire11G
public import CFSG.Quasithin.Vol2.Ch11SecWire11GW
public import CFSG.Quasithin.Vol2.Ch11SecWire11Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt3_2_5W
    (h : PartsW) (hTmpL6_3_2_2_six : TmpL6_3_2_2_six) : H13.Stmt3_2_5 := by
  have hTheorem316Statement :=
    Ch3T316W.theorem316Statement_holds
  exact H13.stmt3_2_5_of_c0 hTheorem316Statement h.proved.d310C0 h.inputs.in10.thm3_3_1
      h.proved.tmpL6_3_2_2_two h.proved.lem3_2_2_eight h.proved.tmpL6_3_2_2_four hTmpL6_3_2_2_six
      h.proved.asB56

end CFSG.Quasithin.Vol2.Ch11.Wire11
