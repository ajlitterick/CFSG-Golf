module

public import CFSG.ClassicalInvolution.AschTight.Basic
public import CFSG.ClassicalInvolution.AschTight.Lemma33

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


omit [Finite G] in
theorem commute_of_commutator_mem_center (hK : Group.IsPerfect K) {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ (Subgroup.center K).map K.subtype) :
    ∀ k ∈ K, k * t = t * k := by
  have hmemK : ∀ k : K, (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ K := fun k =>
    commutator_mem_of_mem_normalizer htN k.2
  have hcen : ∀ k : K, (⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩ : K) ∈ Subgroup.center K := by
    intro k
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (h k k.2)
    have hc' : c = ⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩ := Subtype.ext hce
    rw [← hc']
    exact hc
  let _ : CommGroup (Subgroup.center K) :=
    { (inferInstance : Group (Subgroup.center K)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : K →* Subgroup.center K :=
    { toFun := fun k => ⟨⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩, hcen k⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun k k' => by
        apply Subtype.ext
        apply Subtype.ext
        change (k : G) * k' * t * ((k : G) * k')⁻¹ * t⁻¹ =
          ((k : G) * t * (k : G)⁻¹ * t⁻¹) * ((k' : G) * t * (k' : G)⁻¹ * t⁻¹)
        have hk' : (k : G) * ((k' : G) * t * (k' : G)⁻¹ * t⁻¹) =
            ((k' : G) * t * (k' : G)⁻¹ * t⁻¹) * k :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen k') k)
        rw [commutator_mul hk']
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen k) ⟨_, hmemK k'⟩) }
  intro k hk
  have h1 := eq_one_of_perfect φ ⟨k, hk⟩
  have h2 : k * t * k⁻¹ * t⁻¹ = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
  calc k * t = k * t * k⁻¹ * t⁻¹ * (t * k) := by group
    _ = t * k := by rw [h2, one_mul]


end CFSG.ClassicalInvolution.Disconnected.AschTight
