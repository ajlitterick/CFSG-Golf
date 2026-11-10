module

public import CFSG.Quasithin.Background.ShultG53Layers
public import CFSG.Quasithin.Background.ShultG53IdentPack

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv

instance decMemG5 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Perm.sign σ = 1 ∧ ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

instance decMemCA (σ : Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1))


@[expose] def linePred : Fin 2 → V4 → Prop
  | 0 => predLine4a
  | 1 => predLine4b


end CFSG.Quasithin.ShultG53
