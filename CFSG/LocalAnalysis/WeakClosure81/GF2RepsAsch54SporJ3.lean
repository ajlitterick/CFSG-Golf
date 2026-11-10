module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc

public section

namespace CFSG.LocalAnalysis.WeakClosure81


open CFSG.QuasithinUnique.Ch1.SporLat in
theorem asch54SporGenAt_j3 :
    Asch54SporGenAt .J3 := by
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.Sporadic.SmallOddCore.j3_outer_card_le
    (L := #[1, 3, 3, 9, 15]) (N := 392445) (k := 7) J3K.S_sylow J3K.complete
    (fun j _ => J3K.S_le_Y j) (fun j hj => ?_)
    (by rw [CFSG.Sporadic.Schreier.card_j3P]; norm_num) (a := 4) (b := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [J3K.member_card hj, J3K.card_S]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81

end
