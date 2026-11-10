module

public import CFSG.ClassicalInvolution.Q3.Q3LSplit

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification

theorem centralizer_pCore_le_of_layer_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y = ⊥) (hlayer : Layer.subgroup Y = ⊥) :
    Subgroup.centralizer ((pCore 2 Y : Subgroup Y) : Set Y) ≤ pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : pPrimeCore 2 Y = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    rw [← hO]
    exact le_sSup ⟨hN.1, (Nat.coprime_two_left).1 hN.2⟩
  have hl : layer Y = ⊥ := by rw [layer_eq_componentClassification]; exact hlayer
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y 2 hcore hl


section Below

@[expose] def SolvableMemberInnerBelow : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → L ≤ T ⊔ Subgroup.centralizer (T : Set Y)


theorem quasisimpleConnected3Comp_of_innerBelow (h : SolvableMemberInnerBelow) :
    QuasisimpleConnected3Comp := by
  intro Y _ _ hBelow hO Λ hΛ hconn hns hC
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Y, IsComponentOf T ⊤ := by
    by_contra hno
    push Not at hno
    exact hC (centralizer_pCore_le_of_layer_eq_bot hO
      (le_bot_iff.mp (sSup_le fun T hT => (hno T hT).elim)))
  have hmemΛ : ∀ L ∈ Λ, L ≤ T ⊔ Subgroup.centralizer (T : Set Y) := by
    intro L hL
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact h Y hBelow hO z L hz T hT
  have htop : T ⊔ Subgroup.centralizer (T : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hΛ.generated]
    exact iSup₂_le hmemΛ
  have hsplit : ∀ L ∈ Λ, L ≤ T ∨ L ≤ Subgroup.centralizer (T : Set Y) := by
    intro L hL
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    by_cases hTz : T ≤ Subgroup.centralizer ({z} : Set Y)
    · exact Or.inr (hz.le_centralizer_of_le_centralizer hT hTz)
    · exact Or.inl (solvableMemberSplit_of_top hO hz htop hTz)
  obtain ⟨L₀, hL₀, hL₀D⟩ : ∃ L ∈ Λ, ¬ L ≤ Subgroup.centralizer (T : Set Y) := by
    by_contra hall
    push Not at hall
    have hY : (⊤ : Subgroup Y) ≤ Subgroup.centralizer (T : Set Y) := by
      rw [← hΛ.generated]
      exact iSup₂_le hall
    have hcen : Subgroup.center T = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hY (Subgroup.mem_top (b : Y))) (a : Y)
        a.2).symm
    have hone : ∀ x : T ⧸ Subgroup.center T, x = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H a => exact (QuotientGroup.eq_one_iff a).mpr (hcen ▸ Subgroup.mem_top a)
    obtain ⟨x, y, hxy⟩ := @exists_pair_ne _ hT.2.2.2.toNontrivial
    exact hxy ((hone x).trans (hone y).symm)
  have hL₀T : L₀ ≤ T := (hsplit L₀ hL₀).resolve_right hL₀D
  have hall : ∀ v : ↥Λ, (nonCommGraph Λ).Reachable ⟨L₀, hL₀⟩ v → (v : Subgroup Y) ≤ T := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact hL₀T
    | @tail b c _ hadj ih =>
      rcases hsplit (c : Subgroup Y) c.2 with h | h
      · exact h
      · exfalso
        obtain ⟨-, hnc⟩ := nonCommGraph_adj.mp hadj
        exact hnc fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h hy) x (ih hx)
  have htopT : T = ⊤ := by
    rw [eq_top_iff, ← hΛ.generated]
    exact iSup₂_le fun M hM => hall ⟨M, hM⟩ (hconn.preconnected _ _)
  have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
  subst htopT
  exact Components.quasisimple_of_equiv Subgroup.topEquiv.symm hqs


end Below

section Full


end Full

end CFSG.ClassicalInvolution.Q3
