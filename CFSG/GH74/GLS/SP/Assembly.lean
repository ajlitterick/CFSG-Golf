module

public import CFSG.GH74.GLS.SP.GlueBN
public import CFSG.GH74.GLS.SP.Final

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def SPGlueData (G : Type) [Group G] (F : Type) [Field F] (hF : 4 ≤ Nat.card F) : Prop :=
  ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
    (R : RGD2 4 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧
    ∃ φ : U ≃* (modelSystem F hF).U, ∀ i : ℤ, 1 ≤ i → i ≤ 4 → ∀ x : U,
      (x : G) ∈ root i ↔
        ((φ x : (modelSystem F hF).U) : StatedProj (StatedSp 2 F)) ∈ (modelSystem F hF).root i

theorem spRankTwoData_of_glueData {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    {hF : 4 ≤ Nat.card F} (h : SPGlueData G F hF) : SPRankTwoData G F hF := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  exact ⟨(R.toPre hgen).toSystemOfSimple, φ, hφ⟩

theorem sp_of_glueData {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    {hF : 4 ≤ Nat.card F} (h : SPGlueData G F hF) : Nonempty (G ≃* StatedProj (StatedSp 2 F)) :=
  sp_of_rankTwoData hF (spRankTwoData_of_glueData h)


end CFSG.GH74.GLS.SP
