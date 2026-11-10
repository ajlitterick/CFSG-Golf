module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDiagonal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag
open scoped commutatorElement

theorem scalars_four_eq_bot (K : Type*) [Field K] [CharP K 2] : scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) - 1) ^ 4 = 0 := by
      have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      linear_combination h4 + (-2 * (c : K) ^ 3 + 3 * (c : K) ^ 2 - 2 * (c : K) + 1) *
        (CharP.cast_eq_zero K 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  change (A : Matrix (Fin 4) (Fin 4) K) = 1
  rw [hA, hc1, map_one]

@[expose] def projectiveSLFourEquivSL (K : Type*) [Field K] [CharP K 2] :
    projectiveSL 4 K ≃* SpecialLinearGroup (Fin 4) K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_four_eq_bot K)).trans QuotientGroup.quotientBot

theorem ker_eq_bot_of_sylow_le_map {E G : Type*} [Group E] [Group G] [Finite E]
    [Group.IsPerfect E] (η : E →* G) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) (S : Sylow 2 G) (P₀ : Subgroup E) (hS : (S : Subgroup G) ≤ P₀.map η)
    (hinj : ∀ z ∈ P₀, η z = 1 → z = 1) : η.ker = ⊥ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  have comm_eq : ∀ {a a' b b' : E}, η a = η a' → η b = η b' → ⁅a, b⁆ = ⁅a', b'⁆ :=
    fun ha hb => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker ha hb
  obtain ⟨P, hP, hzP⟩ := exists_sylow_map_eq_twoPart_le η hη hC S
  have hlift : ∀ g ∈ (P : Subgroup E), ∃ p ∈ P₀, η p = η g := fun g hg => by
    have h1 : η g ∈ (P : Subgroup E).map η := mem_map_of_mem η hg
    rw [hP] at h1
    obtain ⟨p, hp, hpg⟩ := mem_map.mp (hS h1)
    exact ⟨p, hp, hpg⟩
  have hPP : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ P₀ := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨p₁, hp₁, h₁⟩ := hlift g₁ hg₁
    obtain ⟨p₂, hp₂, h₂⟩ := hlift g₂ hg₂
    rw [comm_eq h₁.symm h₂.symm, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp₁ hp₂) (inv_mem hp₁)) (inv_mem hp₂)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, hk⟩ := h2 ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact mem_bot.mpr (hinj z (hPP (hzP z hz ⟨k, hk'⟩)) hz)


theorem mul_self_ne_one {K : Type*} [Field K] [CharP K 2] {c : K} (hc : c ≠ 1) : c * c ≠ 1 := by
  intro h
  apply hc
  have h' : (c - 1) ^ 2 = 0 := by
    linear_combination h + (1 - c) * (CharP.cast_eq_zero K 2)
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')

section Diagonal


end Diagonal

section Four


end Four


end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
