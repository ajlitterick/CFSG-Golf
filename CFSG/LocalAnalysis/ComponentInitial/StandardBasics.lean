module

public import CFSG.Assembly.ComponentTypeDefs
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly CFSG.Assembly.ComponentType Polynomial
open scoped commutatorElement

theorem finite_odd_field_two_squares {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (c : k) : ∃ a b : k, a ^ 2 + b ^ 2 = c := by
  have := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 :=
    Nat.mod_two_ne_zero.1 fun h => hk (FiniteField.even_card_iff_char_two.2 h)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (f := (X ^ 2 : k[X]))
    (g := X ^ 2 - C c) (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _) hodd
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

section FusedLift

variable {E J : Type*} [Group E] [Group J]


theorem commutatorElement_mul_right_of_mem_center {x y z : E}
    (hz : ⁅x, z⁆ ∈ Subgroup.center E) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h := Subgroup.mem_center_iff.1 hz
  have : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this, h y, mul_assoc ⁅x, z⁆, mul_inv_cancel, mul_one]


variable {η : E →* J}


end FusedLift

section Standard

variable {G : Type*} [Group G]

theorem standard_involution_centralizer_normality [Finite G] {L : Subgroup G}
    (hL : IsStandardSubgroup L) {t : G} (ht : t ∈ Subgroup.centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      L ≤ Subgroup.centralizer ({t} : Set G) ∧
      (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal ∧
      IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
      ((Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf
        (Subgroup.centralizer ({t} : Set G))).Normal := by
  obtain ⟨hq, -, hodd, hnorm, -⟩ := hL
  set C := Subgroup.centralizer (L : Set G)
  set T := Subgroup.centralizer ({t} : Set G)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hodd ht ht2
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hnorm ▸ hTC
  have hLT : L ≤ T := fun l hl => Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 ht l hl).symm
  have hLn : (L.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLT).2 hTL
  refine ⟨hTL, hLT, hLn, ⟨hLT, IsSubnormal.step hLT hLn (IsSubnormal.refl T), hq⟩, ?_⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
  exact (le_inf hTC (Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf

end Standard

end CFSG.LocalAnalysis.ComponentInitial
