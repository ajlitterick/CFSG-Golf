module

public import CFSG.CharacterTheory.Wreathed.LocalNormalizerActions
public import CFSG.CharacterTheory.Wreathed.BaseSquares
public import CFSG.CharacterTheory.Wreathed.VCyclicFusion

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G]

@[expose] def modelCenter {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.Z m).map (wreathModelHom S e)

@[expose] def modelQ {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.Q m).map (wreathModelHom S e)

@[expose] def modelQEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.Q m ≃* modelQ S e :=
  (Original.Q m).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)


theorem modelVNormalizer_swap_fusion [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : G, g ∈ Subgroup.normalizer (modelV S e : Set G) ∧
      (g * wreathModelHom S e (Original.z (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      g * wreathModelHom S e (Original.z (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))) := by
  obtain ⟨h, _, _, horder⟩ := modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  have hquot : orderOf (originalVQuotientAutomorphism n (modelVAction S e h)) = 3 := horder
  obtain ⟨i, _, hi⟩ := originalVAutomorphism_order_three_swap_endpoint n hn
    (modelVAction S e h) hquot
  have hpoint : wreathModelHom S e (((modelVAction S e h) ^ i)
      (originalVSwap (2 ^ n))).val =
      (h ^ i).val * wreathModelHom S e (Original.z (2 ^ n)) * (h ^ i).val⁻¹ := by
    rw [← map_pow]
    exact modelVAction_coe S e (h ^ i) (originalVSwap (2 ^ n))
  refine ⟨(h ^ i).val, (h ^ i).property, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl (hpoint.symm.trans (congrArg (wreathModelHom S e) hi))
  · exact Or.inr (hpoint.symm.trans (congrArg (wreathModelHom S e) hi))


@[expose] def modelQAutomorphism (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) : MulAut (modelQ S e) :=
  MulAut.congr (modelQEquiv S e)
    (originalQuaternionAutomorphism n hn (modelVAction S e g))

theorem modelQAutomorphism_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) (q : modelQ S e) :
    (modelQAutomorphism n hn S e g q).val = g.val * q.val * g.val⁻¹ := by
  obtain ⟨w, rfl⟩ := (modelQEquiv S e).surjective q
  have happ : modelQAutomorphism n hn S e g (modelQEquiv S e w) =
      modelQEquiv S e (originalQuaternionAutomorphism n hn (modelVAction S e g) w) := by
    change modelQEquiv S e (originalQuaternionAutomorphism n hn (modelVAction S e g)
      ((modelQEquiv S e).symm (modelQEquiv S e w))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [happ]
  change wreathModelHom S e
    (originalQuaternionAutomorphism n hn (modelVAction S e g) w).val =
      g.val * wreathModelHom S e w.val * g.val⁻¹
  rw [originalQuaternionAutomorphism_coe]
  exact modelVAction_coe S e g (Subgroup.inclusion (original_quaternion_le_v n hn) w)

theorem modelVNormalizer_normalizes_modelQ (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ≤
      Subgroup.normalizer (modelQ S e : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact (modelQAutomorphism_coe n hn S e ⟨g, hg⟩ ⟨x, hx⟩) ▸
      (modelQAutomorphism n hn S e ⟨g, hg⟩ ⟨x, hx⟩).property
  · intro hx
    have h := (modelQAutomorphism n hn S e ⟨g⁻¹,
      (Subgroup.normalizer (modelV S e : Set G)).inv_mem hg⟩ ⟨g * x * g⁻¹, hx⟩).property
    rw [modelQAutomorphism_coe] at h
    convert h using 1
    group

theorem modelQAutomorphism_eq_actual_action (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelQAutomorphism n hn S e g =
      (modelQ S e).normalizerMonoidHom
        ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩ := by
  ext q
  rw [modelQAutomorphism_coe]
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe (modelQ S e)
    ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩ q).symm


theorem original_Z_le_center (m : ℕ) : Original.Z m ≤ Subgroup.center (Wreath m) := by
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨i, j, k⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m i j k * Original.a m = Original.a m * element m i j k
  rw [Original.a_eq]
  rcases swap_exponent_cases k with rfl | rfl
  · simp only [element_base_mul, add_comm]
  · rw [element_swap_mul, element_base_mul]
    simp only [add_comm, zero_add]

theorem modelCenterInV_le_center {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelCenter S e).subgroupOf (modelV S e) ≤ Subgroup.center (modelV S e) := by
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hv
  obtain ⟨q, hq, hqw⟩ := Subgroup.mem_map.mp w.property
  change (w : G) * (v : G) = (v : G) * (w : G)
  change wreathModelHom S e z = (v : G) at hzv
  rw [← hzv, ← hqw, ← map_mul, ← map_mul]
  exact congrArg (wreathModelHom S e)
    (Subgroup.mem_center_iff.mp (original_Z_le_center m hz) q)

instance modelCenterInV_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    ((modelCenter S e).subgroupOf (modelV S e)).Normal :=
  Subgroup.normal_of_le_center (modelCenterInV_le_center S e)


end CFSG.Wreathed
