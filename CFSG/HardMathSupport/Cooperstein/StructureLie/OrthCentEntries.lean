module

public import CFSG.LieType.Universal.Spin.Structure.Entries
public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

@[expose] def kap {n : ℕ} (m : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl m
  | false => .inr m


theorem kap_inj {n : ℕ} {i j : Fin n} {s t : Bool} (h : kap i s = kap j t) : i = j ∧ s = t := by
  cases s <;> cases t <;> simp_all [kap]


end CFSG.HardMathSupport.Cooperstein.StructureLie
