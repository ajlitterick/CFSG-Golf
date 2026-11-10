module

public import CFSG.ClassicalInvolution.Q3.Q3T8B04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Plain

structure LinkAxis3 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (z t : G) (B : Subgroup G) : Prop where
  pair_le : Subgroup.closure ({t, z} : Set G) ≤ B
  balance : RankThreeBalance B
  link : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
    ∃ y ∈ rankTwoSpan B, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t'

structure E4Axis {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J R : Subgroup G)
    (z t s : G) : Prop where
  sq : s * s = 1
  ne_one : s ≠ 1
  comm_z : z * s = s * z
  comm_t : t * s = s * t
  indep : s ∉ Subgroup.closure ({z, t} : Set G)
  mem_X : s ∈ omegaNbrGen Ω K
  cent_R : ∀ r ∈ R, r * s = s * r
  norm_J : conjSub s J = J
  nbr₁ : ∃ J₁ ∈ omegaNbr Ω K, IsUniqueInvolution J₁ s
  nbr₂ : ∃ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s)

end Plain

section Defs


end Defs

section Route


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.false_of_linkAxis [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : LinkAxis3 Ω K z t B) : False := by
  have hD := h.isElemAbelian2_pair
  have hD4 : Nat.card ↥(Subgroup.closure ({t, z} : Set G)) = 4 := by simpa using hD.1
  have hodd := odd_card_alphaOf_of_rankThreeBalance hB.balance hB.pair_le hD4
  have heq : ∀ F ∈ signalizerFunctorEk 2 2 B,
      alphaOf F = alphaOf (Subgroup.closure ({t, z} : Set G)) := fun F hF =>
    alphaOf_eq_alphaOf_of_rankThreeBalance hB.balance hF.1 hB.pair_le (by simpa using hF.2) hD4
  have hspan : rankTwoSpan B ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
    unfold rankTwoSpan
    exact iSup₂_le fun F hF => T8T.centralizer_le_normalizer_of_alphaOf_eq (heq F hF)
  refine h.false_of_linkConst (fun J' hJ' t' ht' => ?_) hodd
  obtain ⟨y, hy, hyz, hyt⟩ := hB.link J' hJ' t' ht'
  have h1 : conjSub y (Subgroup.closure ({t, z} : Set G)) =
      Subgroup.closure ({t', z} : Set G) := by
    rw [conjSub_closure_pair, hyz, hyt]
  have h2 := mem_normalizer_iff_conjSub_eq.mp (hspan hy)
  rw [← h1, alphaOf_conjSub]
  exact h2


end Route

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
