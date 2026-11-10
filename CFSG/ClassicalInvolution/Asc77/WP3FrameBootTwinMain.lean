module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCNine
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Stmt
public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.MilestoneAssemblyCore
public import CFSG.Sporadic.Bridge.M11CheckInputs
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem localLeviComponent_of_exact_of_quasisimple
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) {z : G}
    (D : LocalLieSystemAt p f (exactFamily Ω z) z) (i : Fin D.card)
    (hi : (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
      HasA2Pairs (D.tag i)) :
    LocalLeviComponent p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_quasisimple hcls hqs)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      ∀ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ∀ i : Fin D.card,
        ((D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
          HasA2Pairs (D.tag i)) →
        ∃ D' : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
          (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ∃ i' : Fin D'.card,
          (D'.tag i' = .PSL ∧ 3 ≤ D'.rank i') ∨ D'.tag i' = .PSU ∨ D'.tag i' = .PSp ∨
            HasA2Pairs (D'.tag i') := by
    intro S₁ S₂ h D i hi
    subst h
    exact ⟨D, i, hi⟩
  obtain ⟨D', i', hi'⟩ := key _ _ h D i hi
  exact LocalLeviComponent.of_levi D' i' hi'

theorem TwinShapeCtx.listed_levi {z : G} (C : TwinShapeCtx p f Ω z) :
    (C.D.tag C.i₁ = .PSL ∧ 3 ≤ C.D.rank C.i₁) ∨ C.D.tag C.i₁ = .PSU ∨ C.D.tag C.i₁ = .PSp ∨
      HasA2Pairs (C.D.tag C.i₁) := by
  rcases C.listed with ⟨h, -⟩ | ⟨h, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inr (Or.inl h)))))

theorem TwinShapeCtxCore.listed_levi {z : G} (C : TwinShapeCtxCore p f Ω z) :
    ((C.D.tag C.i₁ = .PSL ∧ 3 ≤ C.D.rank C.i₁) ∨ C.D.tag C.i₁ = .PSU ∨ C.D.tag C.i₁ = .PSp ∨
      HasA2Pairs (C.D.tag C.i₁)) ∨ C.D.tag C.i₁ = .G2 := by
  rcases C.listed with (⟨h, -⟩ | ⟨h, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | h
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inl ⟨h, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by
      unfold HasA2Pairs; exact Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr h

end Levi

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def AEmptyTwinExact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → TwinExactShape p f K z →
        ∀ M ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) M

@[expose] def TwinFrameGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      TwinLieShape p f Ω z →
        CentralizerGenerationStar Ω (Subgroup.closure ({z, u, t} : Set G)) t

end Inputs

section Frames


end Frames

end CFSG.ClassicalInvolution.Asc77
