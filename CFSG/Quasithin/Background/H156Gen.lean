module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code


section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem congrHom_apply_eg (eg : V ≃* W) (g : MulAut V) (v : V) :
    congrHom eg g (eg v) = eg (g v) := by
  rw [congrHom_apply, MulEquiv.symm_apply_apply]


end Transport

end CFSG.Quasithin.H156
