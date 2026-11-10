module

public import CFSG.GH74.GLS.SP.Model
public import CFSG.GH74.GLS.SP.Identify
public import CFSG.GH74.GLS.Statements

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def SPRankTwoData (G : Type) [Group G] (F : Type) [Field F] (hF : 4 ≤ Nat.card F) : Prop :=
  ∃ (D : RankTwoSystem G 4) (φ : D.U ≃* (modelSystem F hF).U),
    ∀ i : ℤ, 1 ≤ i → i ≤ 4 → ∀ x : D.U,
      (x : G) ∈ D.root i ↔
        ((φ x : (modelSystem F hF).U) : StatedProj (StatedSp 2 F)) ∈ (modelSystem F hF).root i

theorem sp_of_rankTwoData {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    (hF : 4 ≤ Nat.card F) (h : SPRankTwoData G F hF) :
    Nonempty (G ≃* StatedProj (StatedSp 2 F)) := by
  obtain ⟨D, φ, hφ⟩ := h
  have := isSimpleGroup_model F hF
  exact nonempty_mulEquiv_of_rankTwo D (modelSystem F hF) φ
    (fun i h1 h4 x => hφ i h1 (by exact_mod_cast h4) x)


theorem exists_model_of_lieModel_psp {Gs : Type} [Group Gs] {p f : ℕ}
    (h : LieModel Gs .PSp 2 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Gs ≃* StatedProj (StatedSp 2 K)) := by
  rcases h with ⟨-, -, K, hK, hfin, hcard, he⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨K, hK, hfin, hcard, he⟩
  all_goals omega


end CFSG.GH74.GLS.SP
