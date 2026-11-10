module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem isUniqueInvolution_central {L : Subgroup G} {z : G} (h : IsUniqueInvolution L z) {r : G}
    (hr : r ∈ L) : z * r = r * z := by
  have hy : r * z * r⁻¹ ∈ L := L.mul_mem (L.mul_mem hr h.mem) (L.inv_mem hr)
  have hy2 : (r * z * r⁻¹) * (r * z * r⁻¹) = 1 := by
    calc r * z * r⁻¹ * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  rcases h.unique _ hy hy2 with h1 | h1
  · exact absurd (by simpa using h1) h.ne_one
  · calc z * r = r * z * r⁻¹ * r := by rw [h1]
      _ = r * z := by group

theorem isUniqueInvolution_comap {H : Type} [Group H] {ψ : H →* G}
    (hinj : Function.Injective ψ) {R : Subgroup H} {z : G}
    (hz : IsUniqueInvolution (R.map ψ) z) : ∃ c : H, ψ c = z ∧ IsUniqueInvolution R c := by
  obtain ⟨c, hcR, hcz⟩ := hz.mem
  refine ⟨c, hcz, ⟨hcR, fun h => hz.ne_one ?_, hinj ?_, fun y hy hy2 => ?_⟩⟩
  · rw [← hcz, h, map_one]
  · rw [map_mul, map_one, hcz]
    exact hz.sq
  · have h1 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases hz.unique (ψ y) ⟨y, hy, rfl⟩ h1 with h | h
    · exact Or.inl (hinj (by rw [h, map_one]))
    · exact Or.inr (hinj (by rw [h, hcz]))

@[expose] def conjStabilizer (S : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ J : Subgroup G, conjSub g J ∈ S ↔ J ∈ S}
  one_mem' := fun J => by simp
  mul_mem' := fun {a b} ha hb J => by rw [conjSub_mul, ha, hb]
  inv_mem' := fun {a} ha J => by
    rw [← ha (conjSub a⁻¹ J), conjSub_conjSub_inv]

theorem mem_conjStabilizer_iff {S : Set (Subgroup G)} {g : G} :
    g ∈ conjStabilizer S ↔ ∀ J : Subgroup G, conjSub g J ∈ S ↔ J ∈ S := Iff.rfl

theorem normalizer_iff_conjSub_eq {n : G} {K : Subgroup G} :
    n ∈ Subgroup.normalizer (K : Set G) ↔ conjSub n K = K := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [mem_conjSub_iff]
    have := h (n⁻¹ * x * n)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    exact this
  · intro h x
    have h1 : n * x * n⁻¹ ∈ conjSub n K ↔ x ∈ K := by
      rw [mem_conjSub_iff, show n⁻¹ * (n * x * n⁻¹) * n = x by group]
    rw [h] at h1
    exact h1.symm


end CFSG.ClassicalInvolution.G2D4Models
