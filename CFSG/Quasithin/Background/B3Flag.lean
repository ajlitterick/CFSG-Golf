module

public import CFSG.Quasithin.Background.B3Rank

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}

@[expose] def IsTinv (T : Subgroup (Gp n)) (S : Subgroup (Mod.V n k)) : Prop :=
  ∀ t ∈ T, ∀ s ∈ S, Mod.act n k t s ∈ S


end CFSG.Quasithin.B3
