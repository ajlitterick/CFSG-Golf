module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2NoDih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2DihB
public import CFSG.Quasithin.EmptyFaithful.S143SC
public import CFSG.Quasithin.EmptyFaithful.S143SD
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge.Asc72

namespace S143

namespace InspW2

theorem nonempty_mulEquiv_psu3 {G : Type} [Group G] {s : ℕ} (hs : 2 ≤ s)
    (hG : StatedClassicalModel G .PSU 3 2 s) : Nonempty (G ≃* CFSG.Open.PSU3 2 s) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hG
  have hcard : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  let e' : G ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ s)) := e
  exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative s hs hcard)⟩

theorem noD8_of_psu3 {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) : NoD8 D := by
  intro a b ha hb hab
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3 hf hD
  have hB : IsBenderGroup D :=
    .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr (show CFSG.Open.PSU3 2 f = PSU3Model f from rfl)))
  obtain ⟨S, hS⟩ := (isPGroup_closure_dihedral ha hb hab).exists_le_sylow
  have haS : a ∈ (S : Subgroup D) := hS (Subgroup.subset_closure (by simp))
  have hbS : b ∈ (S : Subgroup D) := hS (Subgroup.subset_closure (by simp))
  exact (IsBenderGroup.commute_of_mul_self_eq_one hB S haS ha b hbS).eq

theorem resW_u34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2 := by
  intro L _ _ _ hF Gc _ _ ρ ž Ŝ Kh hin _
  obtain ⟨-, hsimple⟩ := ClassicalGroups.Unitary.fam_PSU_simplicity L 3 2 2 hF
  obtain ⟨h1, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound L 3 2 2 hF
  have hcard : Nat.card L = 62400 := by
    have h2 : (Nat.card L : ℤ) = 62400 := by
      have h := h1
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
    exact_mod_cast h2
  have hZ : Subgroup.center L = ⊥ :=
    center_eq_bot_of_simple hsimple (by rw [hcard]; norm_num)
  have h6 : 2 ^ 6 ∣ Nat.card L := ⟨975, by rw [hcard]; norm_num⟩
  obtain ⟨-, a', b', -, -, -, ha', hb', hab, hab4⟩ := exists_dihedral_in_inn hZ h6 hin
  exact hab (noD8_of_psu3 (le_refl 2) hF a' b' ha' hb' hab4)

end InspW2

end S143

end CFSG.Quasithin
