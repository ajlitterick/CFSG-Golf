module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem generatedPairGrowth_involutions_normalize_product {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) :
    z ∈ Subgroup.normalizer (Subgroup.zpowers (z * t) : Set G) ∧
      t ∈ Subgroup.normalizer (Subgroup.zpowers (z * t) : Set G) := by
  have hzinv := inv_eq_self_of_orderOf_eq_two hz
  have htinv := inv_eq_self_of_orderOf_eq_two ht
  have hzz : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have hzconj : z * (z * t) * z⁻¹ = (z * t)⁻¹ := by
    calc
      z * (z * t) * z⁻¹ = t * z := by rw [← mul_assoc z z t, hzz, one_mul, hzinv]
      _ = (z * t)⁻¹ := by rw [mul_inv_rev, hzinv, htinv]
  have htconj : t * (z * t) * t⁻¹ = (z * t)⁻¹ := by
    calc
      t * (z * t) * t⁻¹ = t * z := by group
      _ = (z * t)⁻¹ := by rw [mul_inv_rev, hzinv, htinv]
  constructor
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (z * (z * t) * z⁻¹) = _
    rw [hzconj, Subgroup.zpowers_inv]
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * (z * t) * t⁻¹) = _
    rw [htconj, Subgroup.zpowers_inv]

theorem generatedPairGrowth_two_involutions_product_normal {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t = ⊤) :
    (Subgroup.zpowers (z * t)).Normal := by
  have hn := generatedPairGrowth_involutions_normalize_product hz ht
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le (Subgroup.zpowers_le.mpr hn.1) (Subgroup.zpowers_le.mpr hn.2)


theorem generatedPairGrowth_not_two_involutions_generate [IsSimpleGroup G]
    {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hnonabelian : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.zpowers z ⊔ Subgroup.zpowers t ≠ ⊤ := by
  intro hgen
  have hn := generatedPairGrowth_two_involutions_product_normal hz ht hgen
  let : (Subgroup.zpowers (z * t)).Normal := hn
  have hcyclic : IsCyclic G := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (z * t)) with hc | hc
    · have hzt : z * t = 1 := Subgroup.mem_bot.mp (hc ▸ Subgroup.mem_zpowers (z * t))
      have htz : t = z := by
        calc
          t = z⁻¹ * (z * t) := by group
          _ = z⁻¹ := by rw [hzt, mul_one]
          _ = z := inv_eq_self_of_orderOf_eq_two hz
      have hzgen : Subgroup.zpowers z = ⊤ := by simpa only [htz, sup_idem] using hgen
      exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z, hzgen⟩
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z * t, hc⟩
  let : IsCyclic G := hcyclic
  let : CommGroup G := IsCyclic.commGroup
  obtain ⟨a, b, hab⟩ := hnonabelian
  exact hab (mul_comm a b)

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
