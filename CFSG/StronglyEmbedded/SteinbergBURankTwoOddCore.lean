module

public import CFSG.StronglyEmbedded.SteinbergBKSylowInheritance
public import CFSG.GroupTheory.StronglyEmbeddedInvolution
public import CFSG.LocalAnalysis.Asc75.Helpers
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StronglyEmbedded.SteinbergBU

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_of_forall {p : ℕ} {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1) :
    IsElementaryAbelian p A := CFSG.IsElementaryAbelian.of_forall hcomm hexp

variable [Finite G]

theorem exists_four_group_of_two_le_pRank (h : 2 ≤ CFSG.pRank 2 G) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hE, hcard⟩


end CFSG.StronglyEmbedded.SteinbergBU
