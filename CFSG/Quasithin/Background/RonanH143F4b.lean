module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def vecOf (t : Fin 16) : Fin 2 → F4 :=
  ![⟨((t : ℕ) % 2 : ℕ), ((t : ℕ) / 2 % 2 : ℕ)⟩, ⟨((t : ℕ) / 4 % 2 : ℕ), ((t : ℕ) / 8 % 2 : ℕ)⟩]


end CFSG.Quasithin.RonanH143
