module

public import CFSG.Quasithin.EmptyFaithful.A38c4Main
public import CFSG.Quasithin.Vol2.Ch11SecA02Main
public import CFSG.Quasithin.Vol2.Ch11SecA03Main
public import CFSG.Quasithin.Vol2.Ch11SecA04Main
public import CFSG.Quasithin.Vol2.Ch11SecAKDe
public import CFSG.Quasithin.Vol2.Ch11SecAKDj
public import CFSG.Quasithin.Vol2.Ch11SecBK2B
public import CFSG.Quasithin.Vol2.Ch11SecOE2E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4G
public import CFSG.Quasithin.Vol2.Ch11SecWire11G
public import CFSG.Quasithin.Vol2.Ch11SecBK2A
public import CFSG.Quasithin.Vol2.Ch11SecOE2C
public import CFSG.Quasithin.Vol2.Ch11SecOE2D
public import CFSG.Quasithin.Vol2.Ch11SecWire11F
public import CFSG.Quasithin.Vol2.Ch11SecWire11Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem kindModuleFacts : SecC.KindModuleFacts :=
  ⟨SecC.factB42SL3_holds, SecC.factB42Sp4_holds, SecC.factB42G2_holds,
    KGNat.factG2DerivedOrder_holds⟩

theorem stmt11_1_0 (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) : Stmt11_1_0 :=
  SecA.stmt11_1_0_of natFacts KGNat.factG2DerivedOrder_holds h11_0_2 h11_0_3

theorem cartanFacts : SecS.CartanFacts :=
  ⟨SecS.factCartanSL3_holds, SecS.factCartanSp4_holds, G2Q8.factCartanG2_holds⟩

end CFSG.Quasithin.Vol2.Ch11.Wire11
