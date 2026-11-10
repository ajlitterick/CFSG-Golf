module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.ASVolI

@[expose] def burnsideF48t_gf4Mul (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0 else
  if a = 1 then b else if b = 1 then a else
  if a = 2 then (if b = 2 then 3 else 1) else (if b = 2 then 1 else 2)

@[expose] def burnsideF48t_gf4Sq (a : ℕ) : ℕ :=
  if a = 2 then 3 else if a = 3 then 2 else a

section Field


end Field

section Trans

open Matrix


end Trans

end CFSG.ASVolI
