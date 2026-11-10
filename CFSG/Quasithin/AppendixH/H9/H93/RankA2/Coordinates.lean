module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

namespace CFSG.ASVolI.ChH

namespace A2Coords

@[expose] def A2Fixed (x : Fin 4 → ZMod 2) : Prop := x 0 = x 1 ∧ x 2 = x 3

instance : DecidablePred A2Fixed := fun x => inferInstanceAs (Decidable (x 0 = x 1 ∧ x 2 = x 3))

@[expose] def A2Fixes (ε a b : Fin 4 → ZMod 2) : Prop := A2fst ε a b = a ∧ A2snd ε a b = b

instance (ε a b : Fin 4 → ZMod 2) : Decidable (A2Fixes ε a b) :=
  inferInstanceAs (Decidable (A2fst ε a b = a ∧ A2snd ε a b = b))


end A2Coords

end CFSG.ASVolI.ChH
