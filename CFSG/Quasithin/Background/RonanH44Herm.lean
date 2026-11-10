module

public import CFSG.Quasithin.Background.H11Defs
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusRep
public import CFSG.Quasithin.Background.HSU3Borel

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3 CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.G11.Harris.L2 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}


@[expose] def e4 : QIdx ≃ Fin 4 where
  toFun
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr j) => if j = 0 then 2 else 3
  invFun i := match i with
    | 0 => .inl 0
    | 1 => .inr (.inl 0)
    | 2 => .inr (.inr 0)
    | 3 => .inr (.inr 1)
  left_inv i := by
    rcases i with i | i | i
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    · fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl


end CFSG.Quasithin.RonanH44
