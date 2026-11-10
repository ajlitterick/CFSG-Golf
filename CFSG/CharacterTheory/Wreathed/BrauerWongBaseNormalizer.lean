module

public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]


theorem exists_base_three_cycle {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    ∃ Y ∈ Subgroup.normalizer (modelBase S e : Set G),
      Y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * Y =
          wreathModelHom S e (Original.x2 (2 ^ n)) ∧
      Y⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) * Y =
          wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) ∧
      Y⁻¹ * wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) * Y =
          wreathModelHom S e (Original.x (2 ^ n)) := by
  set φ := wreathModelHom S e
  set J := φ (Original.x (2 ^ n))
  set J₁ := φ (Original.x2 (2 ^ n))
  set J₂ := φ (Original.t (2 ^ n) ^ (2 ^ n / 2))
  set T := φ (Original.z (2 ^ n))
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨g₁, hg₁N, hg₁⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hbase
    J J₁ (modelHom_x_mem_modelBase S e) (modelHom_x2_mem_modelBase S e)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.1)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.2.1)
  set Y₀ := g₁⁻¹
  have hY₀N : Y₀ ∈ Subgroup.normalizer (modelBase S e : Set G) :=
    (Subgroup.normalizer _).inv_mem hg₁N
  have hY₀J : Y₀⁻¹ * J * Y₀ = J₁ := by simpa [Y₀] using hg₁
  have hJJ₁ : J * J₁ = J₂ := modelHom_x_mul_x2 S e (by omega)
  have hJ₁J₂ : J₁ * J₂ = J := modelHom_x2_mul_t_half S e
  have hJ₁J : J₁ * J = J₂ := by
    rw [← hJJ₁]
    exact modelBase_commute S e _ _ (modelHom_x2_mem_modelBase S e) (modelHom_x_mem_modelBase S e)
  set u := Y₀⁻¹ * J₁ * Y₀
  have huB : u ∈ modelBase S e :=
    (Subgroup.mem_normalizer_iff''.mp hY₀N J₁).mp (modelHom_x2_mem_modelBase S e)
  have hu2 : orderOf u = 2 := by
    rw [show u = (MulAut.conj Y₀⁻¹) J₁ by simp [u], MulEquiv.orderOf_eq,
      orderOf_injective _ (wreathModelHom_injective S e)]
    exact hstr.involution_orders.2.1
  have huJ₁ : u ≠ J₁ := by
    intro h
    apply modelHom_x_ne_x2 S e (by omega)
    have h' : Y₀⁻¹ * J * Y₀ = Y₀⁻¹ * J₁ * Y₀ := hY₀J.trans h.symm
    exact mul_left_cancel (mul_right_cancel h')
  rcases modelBase_involution_cases S e (by omega) huB hu2 with hu | hu | hu
  ·
    refine ⟨T * Y₀, (Subgroup.normalizer _).mul_mem
      (sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)) hY₀N, ?_, ?_, ?_⟩
    · have hTJ : T⁻¹ * J * T = J := modelHom_x_central S e hn (wreathModelHom_mem S e _)
      calc
        (T * Y₀)⁻¹ * J * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J * T) * Y₀ := by group
        _ = J₁ := by rw [hTJ, hY₀J]
    · calc
        (T * Y₀)⁻¹ * J₁ * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J₁ * T) * Y₀ := by group
        _ = Y₀⁻¹ * (J * J₁) * Y₀ := by rw [modelHom_swap_conj_x2 S e, hJJ₁]
        _ = (Y₀⁻¹ * J * Y₀) * (Y₀⁻¹ * J₁ * Y₀) := by group
        _ = J₂ := by rw [hY₀J, show Y₀⁻¹ * J₁ * Y₀ = J from hu, hJ₁J]
    · calc
        (T * Y₀)⁻¹ * J₂ * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J₂ * T) * Y₀ := by group
        _ = J := by rw [modelHom_swap_conj_t_half S e]; exact hu
  · exact absurd hu huJ₁
  · refine ⟨Y₀, hY₀N, hY₀J, hu, ?_⟩
    calc
      Y₀⁻¹ * J₂ * Y₀ = (Y₀⁻¹ * J * Y₀) * (Y₀⁻¹ * J₁ * Y₀) := by rw [← hJJ₁]; group
      _ = J := by rw [hY₀J, show Y₀⁻¹ * J₁ * Y₀ = J₂ from hu, hJ₁J₂]


omit [Finite G] in
theorem relIndex_eq_card_quotient (C N : Subgroup G) :
    C.relIndex N = Nat.card (N ⧸ C.subgroupOf N) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]


end CFSG.Wreathed.BrauerWong
