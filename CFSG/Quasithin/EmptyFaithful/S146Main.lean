module

public import CFSG.Quasithin.EmptyFaithful.S146Six2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def FinalData146Core (T M : Subgroup G) : Prop :=
  ∃ (H : Subgroup G) (u : G) (H₂ : Subgroup G),
    IsHTM T M H ∧ IsInvU T M H u ∧ IsI T M u (Subgroup.centralizer ({u} : Set G)) ∧
    4 < (pCoreOf 2 H).relIndex T ∧
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
    tZero T u ≤ H₂ ∧
    H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
    Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3)) ∧ ¬ H₂ ≤ M ∧
    Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

@[expose] def Stage146BranchACore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∃ H : Subgroup G, IsHTM T M H ∧ ¬ OddCoreModTwoTrivial H) → FinalData146Core T M

@[expose] def Stage146BranchBCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) → FinalData146Core T M


end CFSG.Quasithin
