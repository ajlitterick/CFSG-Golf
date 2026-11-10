module

public import CFSG.Monster.B.CTIB.Words
public import Certificates.Certificate3011

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem rank_rs
    {i : ℕ} (hi : i < 14) : ((βr (rs i)) - 1).rank = repRanks.getD i 0 := by
  rw [beta_rs]
  exact Certificates.certificate3011 i hi

end CFSG.Monster.B.CTIB
