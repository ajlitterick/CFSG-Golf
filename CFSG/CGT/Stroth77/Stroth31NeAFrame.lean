module

public import CFSG.CGT.Stroth77.Stroth31DAFrame
public import CFSG.CGT.Stroth77.Stroth31Frame
public import CFSG.CGT.Stroth77.Stroth31Wiring
public import CFSG.GroupTheory.PGroup.OmegaComm

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem nsmul_gen_self (n : ℕ) (k : Fin 3 → ℕ) (j : Fin 3) :
    (n • gen k j) j = (n : ZMod (2 ^ k j)) := by
  simp [gen]

theorem nsmul_gen_of_ne (n : ℕ) (k : Fin 3 → ℕ) {i j : Fin 3} (h : i ≠ j) :
    (n • gen k j) i = 0 := by
  simp [gen, Pi.single_eq_of_ne h]


end CFSG.CGT.Stroth77
