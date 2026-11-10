module

public import CFSG.Quasithin.Background.RonanG51Basic
public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6

private instance decMemG5G1 (σ : Equiv.Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Equiv.Perm.sign σ = 1 ∧
    ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

private instance decMemCA6 (σ : Equiv.Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Equiv.Perm.sign σ = 1))

abbrev predLine4a (x : Fin 4 → ZMod 2) : Prop :=
  x = 0 ∨ x = ![1, 0, 0, 0] ∨ x = ![0, 0, 1, 0] ∨ x = ![1, 0, 1, 0]

abbrev predLine4b (x : Fin 4 → ZMod 2) : Prop :=
  x = 0 ∨ x = ![1, 0, 0, 0] ∨ x = ![0, 0, 1, 1] ∨ x = ![1, 0, 1, 1]


end CFSG.Quasithin.RonanG51
