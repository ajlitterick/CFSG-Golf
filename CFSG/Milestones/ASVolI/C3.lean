module

public import CFSG.Quasithin.Background.C35Setup
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.H13.InspC33Holds
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure SetC31 (H R M L V T K : Subgroup G) : Prop where
  hyp : HypC28 H R M L V
  comp : CFSG.Open.IsComponentOf K H
  sylow : IsSylowTwoOf T M
  le_T : R ≤ T
  norm : conjClosure L M ≤ Subgroup.normalizer (K : Set G)
  red : H = conjClosure L M ⊔ conjClosure K T ⊔ T

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC28 H R M L V →
    CFSG.Open.IsComponentOf K H →
    L = conjClosure L M ∧ ((conjClosure L M).subgroupOf M).Normal ∧ conjClosure L M ≤ K ∧
      M ≤ Subgroup.normalizer (K : Set G) ∧ IsPGroup 2 ↥(centerOf K) ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
        C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
        C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
        C31Case10 H R M L V K)

@[expose] def C_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    ∃ K' : Subgroup G, (∃ h ∈ H, K' = conjByElt h K) ∧ L ≤ K' ∧
      conjClosure L M ≤ conjClosure K' T

section BurnsideC33


end BurnsideC33

section


end

@[expose] def C_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → conjClosure L M ≤ conjClosure K T → K = conjClosure K T

section


end

@[expose] def C_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → K = conjClosure K T →
    V ≤ R ⊓ K ∧ ¬ V ≤ Subgroup.centralizer (K : Set G)


@[expose] def C_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → K = conjClosure K T →
    (CFSG.Blueprint.EvenLieType (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSU 3 3 1 (↥K ⧸ Subgroup.center ↥K)) →
    (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K)

end CFSG.ASVolI
