module

public import CFSG.Quasithin.Background.RonanH143Data2
public import CFSG.Quasithin.Background.RonanH143QL
public import CFSG.Quasithin.Background.RonanH143Orb2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin


theorem ePerm_notMem_mog22 : ePerm ∉ mog22 := by
  intro h
  have h0 : ePerm 0 = 0 := (mem_stab_iff 0 _).1 h.1.2
  have : ePerm 0 = 1 := hasArr_ePerm.apply_eq 0 e_ok.2.2.1
  rw [h0] at this
  exact absurd this (by decide)


end CFSG.Quasithin.RonanH143
