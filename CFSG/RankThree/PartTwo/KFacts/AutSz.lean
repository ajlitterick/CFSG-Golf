module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

variable (a : ℕ) (K : Type) [Field K]

@[expose] noncomputable def stdPinnedSz : PinnedAut (suzukiGroup a K) where
  inndiag := (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range
  inn_le := le_rfl
  field := (szFieldAut a K).range
  graph := ∅

variable {a K}

theorem exists_conj_mul_szFieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (suzukiGroup a K)) :
    ∃ (g : suzukiGroup a K) (σ : RingAut K), α = MulAut.conj g * szFieldAut a K σ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  refine ⟨(e.symm α).left, (e.symm α).right, ?_⟩
  rw [← he]
  exact (e.apply_symm_apply α).symm


section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (a K) in
@[expose] def InducesKindSz (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* suzukiGroup a K, InducesKind L (stdPinnedSz a K) e x k


end Induced

end CFSG.RankThree.PartTwo.KFacts
