module

public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ggG0 (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) :
    Subgroup G :=
  L ⊔ ⨆ (y : G) (K : Subgroup G) (_ : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J), K

@[expose] def GGSixHyp (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  (B ≤ Bs ∧ IsElemAbelian p Bs ∧ Nat.card Bs = p ^ pRank p (⊤ : Subgroup G)) ∧
    LargeEvenStdSub p B x L D J ∧
    LargeEvenMarking (ggG0 p B x L D J) (fun _ _ _ I _ θ =>
      Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end Defs

@[expose] def GGHoltAt {G : Type} [Group G] (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ ∃ r : G, orderOf r = 2 ∧ (∀ q : G ⧸ M, r • q = q ↔ q = ((1 : G) : G ⧸ M)) ∧
    ∃ T : Sylow 2 M, r ∈ (T : Subgroup M).map M.subtype ∧
      (T : Subgroup M).map M.subtype ≤ Subgroup.centralizer {r}


theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : InCatalog Y) :
    InCatalog X :=
  CFSG.Assembly.inCatalog_isoInvariant e h

theorem ne_bot_of_isComponentOf' {G : Type} [Group G] {L K : Subgroup G} (hL : IsComponentOf L K) :
    L ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, hsimp⟩ := hL
  obtain ⟨a, b, hab⟩ := hsimp.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp a.2)
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp b.2)
      rw [ha, hb]

section Closing


theorem inCatalog_of_lieModel_std (X : Type) [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : LieModel X t n p f) : InCatalog X := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact ClassicalModels.inCatalog_of_statedClassicalModel X t n p f h
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inl ⟨t, p, f, ht, h⟩)
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inr (.inl ⟨t, p, f, ht, h⟩))
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inr (.inr ⟨p, f, h⟩))


end Closing

end CFSG.StandardType
