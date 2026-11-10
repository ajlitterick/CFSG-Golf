module

public import CFSG.Quasithin.Background.RonanH143QL2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin


theorem notMem_PO_mul_ePerm_sylw {y : P24} (hy : y ∈ PO) : y * ePerm ∉ PO := by
  intro h
  have hPE : ePerm ∈ PO := by
    simpa using PO.mul_mem (PO.inv_mem hy) h
  exact ePerm_notMem_mog22 (PO_le_mog22 hPE)


end CFSG.Quasithin.RonanH143
