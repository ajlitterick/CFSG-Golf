module

public import CFSG.Milestones.ASVolI.H1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin

theorem mQuot_bot_eq_rk {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    E3.mQuot A ⊥ = rk ↥A := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]


end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_10_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M A : Subgroup (MulAut V)), IsA2 M A → xiSub A = E3.gammaCheck (rk ↥A - 1) A


end CFSG.ASVolI
