
module

public import Certificates.Certificate7014Base
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

import CFSG.Quasithin.H13.J4CentralizerPrelude
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.J4Image
meta import CFSG.Sporadic.Schreier.J4SOrbits

public section

namespace Certificates

open CFSG.Quasithin.H13.J4

theorem certificate7014 :
    Nat.card CFSG.Quasithin.H13.J4.W = 21799895040 := by
  refine le_antisymm ?_ ?_
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe W_le_J).toEquiv]
    exact (Subgroup.card_le_of_le W_subgroupOf_le_centralizer).trans card_centralizer_tJ_le
  · have hPW : Nat.card (P.subgroupOf W) = 8192 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_W).toEquiv, card_P]
      norm_num
    have hW : Nat.card rho.ker * Nat.card rho.range = Nat.card W := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hk : 8192 ≤ Nat.card rho.ker := hPW ▸ Subgroup.card_le_of_le P_le_ker_rho
    rw [← hW]
    calc (21799895040 : ℕ) = 8192 * 2661120 := by norm_num
      _ ≤ Nat.card rho.ker * Nat.card rho.range := Nat.mul_le_mul hk le_card_range_rho

end Certificates
