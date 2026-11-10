module

public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.RonanG52

open Equiv CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

namespace Aux

local instance decMemG5G1 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Perm.sign σ = 1 ∧ ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

local instance decMemCA6 (σ : Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1))

local instance decMemT0 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1 ⊓ cA6) :=
  (inferInstance : Decidable (σ ∈ g5G1 ∧ σ ∈ cA6))


end Aux


end CFSG.Quasithin.RonanG52
