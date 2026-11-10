module

public import CFSG.CGT.Stroth77.Arch76FrameChar
public import CFSG.CGT.Stroth77.StrothFrameNE
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.CGT.Stroth77.Stroth31

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem closure_singleton_eq_one_or {s : G} (hs : s * s = 1) {x : G}
    (hx : x ∈ Subgroup.closure ({s} : Set G)) : x = 1 ∨ x = s := by
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Or.inr (by simpa using hy)
  · exact Or.inl rfl
  · intro a b _ _ ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hs, mul_assoc]
  · intro a _ ha
    rcases ha with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right hs)

theorem card_sup_closure_singleton_le_mul_two (H : Subgroup G) {s : G}
    (hs : s * s = 1) (hN : s ∈ Subgroup.normalizer H) :
    Nat.card (H ⊔ Subgroup.closure ({s} : Set G) : Subgroup G) ≤ 2 * Nat.card H := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj : ∀ h ∈ H, s * h * s ∈ H := by
    intro h hh
    have := (Subgroup.mem_normalizer_iff.mp hN h).mp hh
    simpa [hsinv] using this
  let K : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, x = h ∨ x = h * s}
      one_mem' := ⟨1, H.one_mem, Or.inl rfl⟩
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨u, hu, hx⟩
        rcases hb with ⟨v, hv, hy⟩
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact ⟨u * v, H.mul_mem hu hv, Or.inl (by rw [hx, hy])⟩
        · exact ⟨u * v, H.mul_mem hu hv, Or.inr (by rw [hx, hy]; simp [hs, mul_assoc])⟩
        · refine ⟨u * (s * v * s), H.mul_mem hu (hconj v hv), Or.inr ?_⟩
          rw [hx, hy]; simp [hs, mul_assoc]
        · refine ⟨u * (s * v * s), H.mul_mem hu (hconj v hv), Or.inl ?_⟩
          rw [hx, hy]
          calc (u * s) * (v * s) = u * (s * v * s) * (s * s) := by simp [hs, mul_assoc]
            _ = u * (s * v * s) := by simp [hs, mul_assoc]
      inv_mem' := by
        intro x hx
        rcases hx with ⟨u, hu, hx⟩
        rcases hx with hx | hx
        · exact ⟨u⁻¹, H.inv_mem hu, Or.inl (by simpa [hx])⟩
        · refine ⟨s * u⁻¹ * s, hconj u⁻¹ (H.inv_mem hu), Or.inr ?_⟩
          rw [hx]
          calc (u * s)⁻¹ = s * u⁻¹ := by rw [mul_inv_rev, hsinv]
            _ = (s * u⁻¹) * (s * s) := by simp [hs, mul_assoc]
            _ = (s * u⁻¹) := by simp [hs, mul_assoc]
            _ = (s * u⁻¹ * s) * s := by simp [hs, mul_assoc] }
  have hHK : H ≤ K := fun h hh => ⟨h, hh, Or.inl rfl⟩
  have hsK : s ∈ K := ⟨1, H.one_mem, Or.inr (by simp)⟩
  have hclK : Subgroup.closure ({s} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    simpa using hsK
  have hsupK : H ⊔ Subgroup.closure ({s} : Set G) ≤ K := sup_le hHK hclK
  let f : H × Fin 2 → K := fun p =>
    ⟨(p.1 : G) * s ^ (p.2 : ℕ), by
      refine K.mul_mem (hHK p.1.2) ?_
      refine pow_mem ?_ (p.2 : ℕ)
      simpa using hsK⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨h, hh, hx | hx⟩ := hx
    · refine ⟨(⟨h, hh⟩, 0), ?_⟩
      apply Subtype.ext
      simp [f, hx]
    · refine ⟨(⟨h, hh⟩, 1), ?_⟩
      apply Subtype.ext
      simp [f, hx]
  have hKcard : Nat.card K ≤ 2 * Nat.card H := by
    have hcard := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, Nat.card_fin] at hcard
    simpa [Nat.mul_comm] using hcard
  exact (Subgroup.card_le_of_le hsupK).trans hKcard

namespace StrothFrame

theorem card_T_eq (F : StrothFrame G) :
    Nat.card (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} : Subgroup G) = 256 := by
  refine le_antisymm ?_ F.card_T_ge
  exact F.card_le_of_le_normalizer_E F.T_le_normalizer_E
    (F.S.isPGroup'.to_le F.T_le_S)


end StrothFrame


end CFSG.CGT.Stroth77
