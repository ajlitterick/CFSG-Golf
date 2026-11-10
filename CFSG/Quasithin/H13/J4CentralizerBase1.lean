
module

public import CFSG.Quasithin.H13.J4CentralizerBase

public import CFSG.Quasithin.H13.J4ClassesBase1
public meta import CFSG.Sporadic.Schreier.J4SOrbits

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4


theorem tS_eq_tJ : J4Classes.tS = tJ := Subtype.ext J4Classes.tS_coe

theorem isConj_tJ_e1
    : IsConj tJ CFSG.Sporadic.J4Schreier.z := tS_eq_tJ ▸ J4Classes.isConj_tS_z

end CFSG.Quasithin.H13.J4
