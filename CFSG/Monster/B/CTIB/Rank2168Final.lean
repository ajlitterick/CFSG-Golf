module

public import CFSG.Monster.B.CTIB.Rank2168
public import CFSG.Monster.B.CTIB.Rank2158Final

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem native_rank_2168_centralizer_has_no_components :
    ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2168 →
      (∃ R : Subgroup (Subgroup.centralizer {s}), R.Normal ∧ IsPGroup 2 R ∧
        Subgroup.centralizer (R : Set (Subgroup.centralizer {s})) ≤ R) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {s})) ≤ 2 ^ 38 ∧
      ∀ K : Subgroup (Subgroup.centralizer {s}), ¬ CFSG.IsComponent K :=
  native_rank_2168_centralizer_has_no_components_of
    native_rank_2158_distance_three_product_final.2.1

end CFSG.Monster.B.CTIB
