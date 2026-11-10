module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank
public import Mathlib.Data.Finset.Max
public import Batteries.Data.Nat.Bitwise.Lemmas

public section

namespace CFSG.Monster.B.TwoA.Sp8.P0Rank

open MonsterB.P0Rank

@[expose] def XorClosed (S : Finset ℕ) : Prop := 0 ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S


theorem eq_of_card_lt_two_mul {W M : Finset ℕ} (hW : XorClosed W) (hM : XorClosed M)
    (hWM : W ⊆ M) (hc : M.card < 2 * W.card) : W = M := by
  by_contra hne
  obtain ⟨m, hmM, hmW⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hWM, hne⟩)
  let f : ℕ → ℕ := fun w => m ^^^ w
  have hf_inj : Function.Injective f := Nat.xor_right_injective (x := m)
  have hsub : W ∪ W.image f ⊆ M := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxW | hxI
    · exact hWM hxW
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxI
      exact hM.2 m hmM w (hWM hw)
  have hdisj : Disjoint W (W.image f) := by
    rw [Finset.disjoint_left]
    rintro w hwW hwI
    obtain ⟨w', hw', hwx⟩ := Finset.mem_image.mp hwI
    apply hmW
    have hm : m = w ^^^ w' := by
      rw [← hwx, Nat.xor_xor_cancel_right]
    rw [hm]
    exact hW.2 w hwW w' hw'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective W hf_inj] at hcard
  omega

end CFSG.Monster.B.TwoA.Sp8.P0Rank
