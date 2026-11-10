module

public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LieType.Chevalley.CLSEvenE6FieldInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionCentralizerRank

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.E6SecondGraphFixed

section General

variable {G : Type*} [Group G]


theorem two_le_pRank_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : 2 ≤ CFSG.pRank 2 S :=
  two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hS) (by
    rw [center_eq_bot_of_isSimpleGroup hS, Subgroup.card_bot]
    exact odd_one)


end General

theorem exists_ne_comm_of_mulEquiv_adjointGroup_F4
    {k : Type} [Field k] (h2 : (2 : k) = 0)
    {H : Type*} [Group H] (e : H ≃* adjointGroup Tag.F4 k) : ∃ x y : H, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hab : ∀ a b : adjointGroup Tag.F4 k, a * b = b * a := fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul, hcon]
  have hbot : commutator (adjointGroup Tag.F4 k) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [single_edge_perfect Tag.F4 k (Or.inl rfl)] at hbot
  have hx := orderOf_xElement_F4 (k := k) h2
  have h1 : xElement (τ := Tag.F4) ⟨0, by decide⟩ (1 : k) = 1 := by
    have hmem : xElement (τ := Tag.F4) ⟨0, by decide⟩ (1 : k) ∈ (⊤ : Subgroup _) :=
      Subgroup.mem_top _
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [h1, orderOf_one] at hx
  exact absurd hx (by decide)


end CFSG.LieType.Chevalley
