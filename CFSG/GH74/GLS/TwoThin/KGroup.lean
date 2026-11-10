module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.GH74.GLS.TwoThin.G.Pred

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement


@[expose] def TwoThinKGroupVerticalQ (Q : GroupPred) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Q H → ∀ (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀],
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L = L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ L →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupDiagonalQ (Q : GroupPred) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Q H → ∀ (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀]
    (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥),
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L ≠ L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ (swapDiag hAB).range →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupFactQ (Q : GroupPred) : Prop :=
  TwoThinKGroupVerticalQ Q ∧ TwoThinKGroupDiagonalQ Q


end CFSG.GH74.GLS.TwoThin
