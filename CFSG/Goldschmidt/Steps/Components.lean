module

import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

theorem N8a :
    ∀ (G : Type) [Group G] [Finite G] (L H : Subgroup G), IsComponentOf L ⊤ →
      CFSG.Open.IsSubnormal H ⊤ → L ≤ H ∨ ⁅L, H⁆ = ⊥ := fun _ _ _ L H hL hH =>
  LocalComponents.subnormal_contains_or_commutes L H hL hH

theorem N8b :
    ∀ (G : Type) [Group G] [Finite G] (K L : Subgroup G), IsComponentOf K ⊤ → IsComponentOf L ⊤ →
      K ≠ L → ⁅K, L⁆ = ⊥ := fun _ _ _ K L hK hL hne => LocalComponents.commute_of_ne K L hK hL hne

theorem N8c :
    ∀ (G : Type) [Group G] [Finite G] (L N : Subgroup G), IsComponentOf L ⊤ → N.Normal →
      Group.IsSolvable N → ⁅L, N⁆ = ⊥ := fun _ _ _ L N hL hN _ =>
  LocalComponents.commutes_with_solvable_subnormal L N hL
    (Components.chain_of_mathlib_subnormal hN.isSubnormal)

theorem N8d :
    ∀ (G : Type) [Group G] [Finite G], goldschmidtOddCore G = ⊥ →
      (∀ K : Subgroup G, IsComponentOf K ⊤ → IsPGroup 2 (Subgroup.center K)) ∧
      (Subgroup.center (goldschmidtLayer G)).map (goldschmidtLayer G).subtype ≤
        CFSG.Open.pCore 2 G ∧
      Subgroup.centralizer ((CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G : Subgroup G) : Set G) ≤
        CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G := by
  intro G _ _ hO
  have hO' : componentClassificationOddCore G = ⊥ := hO
  have hFit : Fitting.subgroup G = CFSG.Open.pCore 2 G := by
    rw [PrimeCore.fitting_eq_two_of_odd_corefree hO',
      CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
    rfl
  have hE : Layer.subgroup G = goldschmidtLayer G := rfl
  have hZE : (Subgroup.center (goldschmidtLayer G)).map (goldschmidtLayer G).subtype ≤
      CFSG.Open.pCore 2 G := by
    rw [← hFit, ← hE]
    exact GeneralizedFitting.layer_center_le_fitting G
  refine ⟨fun K hK => ?_, hZE, ?_⟩
  · have hle : (Subgroup.center K).map K.subtype ≤ CFSG.Open.pCore 2 G := by
      refine le_trans ?_ hZE
      rintro _ ⟨z, hz, rfl⟩
      have hzE : (z : G) ∈ goldschmidtLayer G := Layer.component_le hK z.2
      have hzc := ComponentAutomorphisms.center_le_layer_center K hK
        (Subgroup.mem_map_of_mem K.subtype hz)
      refine ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun e => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hzc e e.2
    exact ((CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).to_le hle).of_equiv
      ((Subgroup.center K).equivMapOfInjective K.subtype K.subtype_injective).symm
  · have h := GeneralizedFitting.centralizer_le G
    rwa [GeneralizedFitting.subgroup, hFit, hE] at h


theorem N8f :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ α : MulAut K,
      (∀ k : K, α k * k⁻¹ ∈ Subgroup.center K) → α = 1 := fun _ _ _ hK α hα =>
  CFSG.GorensteinWalter.perfect_central_automorphism_eq ⟨hK.1⟩ α 1 (by simpa using hα)

theorem N8g :
    ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), N.Normal → IsSimpleGroup N →
      (∃ a b : N, a * b ≠ b * a) → Subgroup.centralizer (N : Set Y) = ⊥ →
      goldschmidtOddCore Y = ⊥ ∧ CFSG.Open.pCore 2 Y = ⊥ ∧ goldschmidtLayer Y = N ∧
      ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = N := by
  intro Y _ _ N hN hsimple hnonab hcent
  have : Group.IsPerfect N := ⟨Helpers.commutator_eq_top N hnonab⟩
  have hNc : IsComponentOf N ⊤ :=
    ⟨le_top, Components.chain_of_mathlib_subnormal hN.isSubnormal,
      Quasisimple.simple_of_perfect N⟩
  have hbot : ∀ H : Subgroup Y, ⁅N, H⁆ = ⊥ → H = ⊥ := fun H h => by
    rw [← le_bot_iff, ← hcent]
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hcomp : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = N := by
    intro K hK
    by_contra hne
    have hKbot : K = ⊥ := hbot K (by
      rw [Subgroup.commutator_comm]
      exact LocalComponents.commute_of_ne K N hK hNc hne)
    exact (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2)) hKbot
  have hsolv : ∀ M : Subgroup Y, M.Normal → Group.IsSolvable M → M = ⊥ := by
    intro M hM _
    exact hbot M (LocalComponents.commutes_with_solvable_subnormal N M hNc
      (Components.chain_of_mathlib_subnormal hM.isSubnormal))
  refine ⟨?_, ?_, ?_, hcomp⟩
  · exact hsolv _ (goldschmidtOddCore_normal Y)
      (CFSG.Milestones.odd_order_solvable (OddCore.odd_card Y))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := Y) 2).isNilpotent
    exact hsolv _ (CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2) inferInstance
  · exact le_antisymm (sSup_le fun K hK => (hcomp K hK).le) (le_sSup hNc)


end CFSG.Goldschmidt
