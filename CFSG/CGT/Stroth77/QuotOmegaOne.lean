module

public import CFSG.CGT.Stroth77.Section224Deviation

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}


@[expose]
def twoTorsion (k : Fin 3 → ℕ) : AddSubgroup (Torus k) where
  carrier := {v | (2 : ℤ) • v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_neg, ha, neg_zero]

@[simp]
theorem mem_twoTorsion {k : Fin 3 → ℕ} {v : Torus k} :
    v ∈ twoTorsion k ↔ (2 : ℤ) • v = 0 := Iff.rfl

namespace StrothDatum

variable (Z : StrothDatum X)


end StrothDatum

namespace StrothDatum

variable (Z : StrothDatum X)

theorem conjBy_mem_omegaIn_one {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G))
    {d : Z.D} (hd : d ∈ (omegaIn 1 Z.D).subgroupOf Z.D) :
    conjBy hg d ∈ (omegaIn 1 Z.D).subgroupOf Z.D := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, mem_omegaIn_iff_of_comm hcomm] at hd ⊢
  refine ⟨(conjBy hg d).2, ?_⟩
  have hsq : ((d : Z.D) : G) * ((d : Z.D) : G) = 1 := by
    simpa [pow_two] using hd.2
  have hconj : ((conjBy hg d : Z.D) : G) = g⁻¹ * (d : G) * g := rfl
  have h2 : (g⁻¹ * (d : G) * g) * (g⁻¹ * (d : G) * g) = 1 := by
    calc (g⁻¹ * (d : G) * g) * (g⁻¹ * (d : G) * g)
        = g⁻¹ * (((d : Z.D) : G) * ((d : Z.D) : G)) * g := by group
      _ = 1 := by rw [hsq]; group
  rw [hconj]
  simpa [pow_two] using h2

@[expose]
def conjByMul {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) : Z.D →* Z.D where
  toFun d := conjBy hg d
  map_one' := by ext; simp [conjBy]
  map_mul' a b := by ext; simp [conjBy]; group

@[expose]
noncomputable def quotConjBy {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) :
    Z.D ⧸ (omegaIn 1 Z.D).subgroupOf Z.D →* Z.D ⧸ (omegaIn 1 Z.D).subgroupOf Z.D :=
  QuotientGroup.map _ _ (conjByMul Z hg) (fun d hd => Z.conjBy_mem_omegaIn_one hg hd)

@[simp]
theorem quotConjBy_mk {g : G} (hg : g ∈ Subgroup.normalizer (Z.D : Set G)) (d : Z.D) :
    quotConjBy Z hg (QuotientGroup.mk d) = QuotientGroup.mk (conjBy hg d) := rfl

end StrothDatum

end CFSG.CGT.Stroth77
