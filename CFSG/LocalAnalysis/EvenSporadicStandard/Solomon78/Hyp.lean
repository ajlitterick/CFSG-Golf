module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] noncomputable def twoAdic {X : Type*} [Group X] (H : Subgroup X) : ℕ :=
  (Nat.card H).factorization 2

@[expose] noncomputable def componentProduct (K : Subgroup G) (u : G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ centralizer ({u} : Set G) ∧
    (N.subgroupOf (centralizer ({u} : Set G))).Normal ∧ Nonempty (N ≃* K)}

@[expose] def autCentralizer (L K : Subgroup G) : Subgroup (MulAut L) where
  carrier := {α | ∀ k : L, (k : G) ∈ K → α k = k}
  mul_mem' := by
    intro a b ha hb k hk
    show a (b k) = k
    rw [hb k hk, ha k hk]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro a ha k hk
    show a.symm k = k
    calc a.symm k = a.symm (a k) := by rw [ha k hk]
      _ = k := a.symm_apply_apply k

@[expose] def vCandidates (K : Subgroup G) (u : G) : Set G :=
  {v | v ∈ K ⊔ zpowers u ∧ v ∉ (center K).map K.subtype ∧ orderOf v = 2}

@[expose] def vMaximal (K : Subgroup G) (u : G) : Set G :=
  {v | v ∈ vCandidates K u ∧ ∀ v' ∈ vCandidates K u,
    twoAdic (K ⊓ centralizer ({v'} : Set G)) ≤ twoAdic (K ⊓ centralizer ({v} : Set G))}

@[expose] def vPairs (L K : Subgroup G) (u : G) : Set G :=
  {w | ∃ v ∈ vMaximal K u, w = u * v ∧ ∃ l ∈ L, l * u * l⁻¹ = w}


end CFSG.EvenSporadicStandard.Solomon78
