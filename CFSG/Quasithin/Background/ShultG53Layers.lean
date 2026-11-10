module

public import CFSG.Quasithin.Background.ShultG53Chain
public import CFSG.Quasithin.Background.ShultG53Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv


@[expose] def FixList (k : Fin 2) (u : Fn) (L : List (Perm (Fin 6))) : Prop :=
  ∀ σ ∈ L, Perm.sign σ = 1 ∧ ∀ w : V4, u (Matrix.mulVec (Rm k σ⁻¹) w) = u w

instance (k : Fin 2) (u : Fn) (L : List (Perm (Fin 6))) : Decidable (FixList k u L) :=
  inferInstanceAs (Decidable (∀ σ ∈ L, Perm.sign σ = 1 ∧
    ∀ w : V4, u (Matrix.mulVec (Rm k σ⁻¹) w) = u w))


end CFSG.Quasithin.ShultG53
