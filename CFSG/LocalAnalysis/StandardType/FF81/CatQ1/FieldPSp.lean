module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Arith
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem outerThreeBig_of_modelPSp {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSp n ℓ f) : OuterThreeBig K := by
  intro h4 β hβ hout
  have hin : β ∉ inner K := fun ⟨k, hk⟩ => hout k hk.symm
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.psp_pRank_fixed
      hcl Nat.prime_three (by norm_num) β hβ hin
  refine Or.inl (twentySeven_dvd_of_three_le_pRank (fixedSubgroup β) ?_)
  obtain ⟨⟨hℓprime, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  by_cases hℓ3 : ℓ = 3
  · have hcard3 : Nat.card F₀ = 3 ^ (f / 3) := by rw [hcard, hℓ3]
    have hf0 : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
    have hm : StatedClassicalModel (StatedProj (StatedSp n F₀)) .PSp n 3 (f / 3) := by
      refine ⟨⟨Nat.prime_three, hf0, hn, ?_⟩, F₀, hF₀, hF₀fin, hcard3,
        ⟨MulEquiv.refl _⟩⟩
      intro hcon
      have h2 : 3 ^ (f / 3) = 2 := (Prod.mk.inj hcon).2
      have h3dvd : 3 ∣ 3 ^ (f / 3) := dvd_pow_self 3 (by omega)
      exact absurd (h2 ▸ h3dvd) (by norm_num)
    have h3le : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n F₀))) := by
      obtain ⟨-, -, hcases⟩ :=
        CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) hm
      rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, ⟨-, hle⟩ | hle⟩ | hle
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · omega
      · omega
      · omega
    omega
  · have hFcard' : Nat.card F = Nat.card F₀ ^ 3 := by
      rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hpF : ¬ 3 ∣ Nat.card F := by
      rw [hFcard]
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.not_dvd_pow_of_ne
        Nat.prime_three hℓprime hℓ3
    have hK : CFSG.Open.pRank 3 (⊤ : Subgroup K) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n F))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e
    have heq :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_Sp_eq_of_pow
        (n := n) Nat.prime_three (by norm_num) hFcard' hpF
    omega

end CFSG.StandardType.FF81.CatQ1
