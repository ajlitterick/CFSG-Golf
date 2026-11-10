
module

public import CFSG.Monster.B.TwoA.Base.IncidenceBase

public import CFSG.Monster.B.TwoA.Base.Par45A

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B

theorem natCard_Echain :
    ∀ i : ℕ, 1 ≤ i → i ≤ 5 → Nat.card (Echain i) = 2 ^ i := by
  intro i h1 h5
  interval_cases i
  · exact natCard_zpowers_xhat
  · exact natCard_Vhat_pow
  · exact natCard_E3_pow
  · exact natCard_E4
  · exact natCard_E5


attribute [local instance] parAction


end CFSG.Monster.B.TwoA
