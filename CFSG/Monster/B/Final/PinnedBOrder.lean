module

public import CFSG.Monster.B.Final.PairNodes
public import CFSG.Monster.B.CTIB.Defs
public import CFSG.Monster.Existence.BabyOrder

public section

namespace CFSG.Monster.B

open Matrix MulOpposite CFSG.Blueprint CFSG.Monster

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)


theorem pinned_B_explicit_native_isomorphism_simplicity_and_order :
    HB = ⊤ ∧
      (∃ e : NativeSporadic.B ≃* Sbp,
        (∀ X, ((betaRow Dyadic.betaS (e X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
        e bA₁ = aB ∧ e bA₂ = bB) ∧
      Nontrivial NativeSporadic.B ∧ IsSimpleGroup NativeSporadic.B ∧
      Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
  obtain ⟨hH, e, he, h1, h2, hs⟩ := pinned_B_explicit_native_isomorphism CTIB.betaS_explicit
  refine ⟨hH, ⟨e, he, h1, h2⟩, hs.toNontrivial, hs, ?_⟩
  rw [CFSG.Monster.Existence.card_nativeB]
  rfl

end CFSG.Monster.B
