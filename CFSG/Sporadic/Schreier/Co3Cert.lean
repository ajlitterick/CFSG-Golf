
module

public import CFSG.Sporadic.Schreier.Co3CertBase
import all CFSG.Sporadic.Schreier.Co3CertBase

public import CFSG.Sporadic.Schreier.Co3CertCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem co3ChainArrs_inv : ∀ j < co3ChainArrs.size,
    isInvA 276 co3ChainArrs[j]! (rawInvs 276 co3ChainArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  rw [co3ChainArrs_size] at hj
  rw [co3ChainArrs_get hj]
  exact co3Layout_check.2.2.2.2.1 j (by omega)


theorem rep_co3StrongPerm
    {j : ℕ} (hj : j < 14) : Rep 276 co3ChainArrs[j]! (co3StrongPerm j) :=
  (rep_permOfArr (co3ChainArrs_inv j (by rw [co3ChainArrs_size]; exact hj))).1


end CFSG.Sporadic.Schreier.Co3
