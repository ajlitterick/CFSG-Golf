
module

public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

theorem smul_def (k : Kstab v0) (x : Wv v0) : k • x = wAct v0 k⁻¹ x := rfl

theorem decW_inj_valid {a b : ℕ} (ha : validW a = true) (hb : validW b = true)
    (h : decW a = decW b) : a = b :=
  decW_injective (of_decide_eq_true ha) (of_decide_eq_true hb) h


@[expose] def F9 : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure ((fun k => decode fPerms[k]!) '' {k | k < fPerms.size})

end CFSG.Monster.B.TwoA.Co2Inv
