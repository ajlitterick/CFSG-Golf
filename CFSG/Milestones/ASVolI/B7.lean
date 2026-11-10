module

public import CFSG.Milestones.ASVolI.B1

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_7_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ W : Subgroup V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → commSub W A ≠ ⊥ →
        IsFFStarOffender (autSub G W) (autSub A W) ∧
        (IsFFStarMin G A →
          IsFFStarMin (autSub G W) (autSub A W) ∧
          (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
            W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥) ∧
          (¬ IsStrongFFStarOffender (autSub G W) (autSub A W) →
            rk (autSub A W) = rkIdx (fixV (autSub A W)))) ∧
        (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
          (A ⊓ centSub W = ⊥ ∧ W ⊔ fixV A = ⊤) ∨
          (IsFFStarOffender G (A ⊓ centSub W) ∧ FFLe G (A ⊓ centSub W) A))

section BurnsideB7a


end BurnsideB7a


@[expose] def B_7_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ H : Subgroup (MulAut V), H ≠ ⊥ → H ≤ G → twoResidual H = H → ⁅H, A⁆ = H →
        TwoChiefFactorsCentral H →
        (∀ a ∈ A, commSub (commSub ⊤ (Subgroup.zpowers a)) A = ⊥ →
          ∀ I ∈ IrrPlus H ⊤, I.map a.toMonoidHom = I) ∧
        (IsFFStarMin G A → ∀ a ∈ A, ∀ I ∈ IrrPlus H ⊤, I.map a.toMonoidHom = I)


end CFSG.ASVolI
