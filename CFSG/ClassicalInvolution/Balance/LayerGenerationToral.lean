module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

section Index

variable {X : Type*} [Group X]

@[expose] def IndexTwoCentralizes (Ē R : Subgroup X) : Prop :=
  Ē ≤ Subgroup.normalizer (R : Set X) ∧ ∃ a ∈ Ē, ∀ x ∈ Ē,
    (∀ r ∈ R, x * r = r * x) ∨ (∀ r ∈ R, (x * a) * r = r * (x * a))

private theorem exists_two_ne_one_of_card_eq_four'' {F₀ : Subgroup X} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

theorem exists_ne_one_centralizes_of_indexTwo {Ē R F : Subgroup X} (hE2 : ∀ x ∈ Ē, x * x = 1)
    (hFĒ : F ≤ Ē) (hF4 : Nat.card F = 4) (h : IndexTwoCentralizes Ē R) :
    ∃ f ∈ F, f ≠ 1 ∧ ∀ r ∈ R, f * r = r * f := by
  obtain ⟨-, a, haĒ, hsplit⟩ := h
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one_of_card_eq_four'' hF4
  by_cases hxR : ∀ r ∈ R, x * r = r * x
  · exact ⟨x, hx, hx1, hxR⟩
  by_cases hyR : ∀ r ∈ R, y * r = r * y
  · exact ⟨y, hy, hy1, hyR⟩
  have hxa := (hsplit x (hFĒ hx)).resolve_left hxR
  have hya := (hsplit y (hFĒ hy)).resolve_left hyR
  have hxy' : ∀ r ∈ R, (x * y) * r = r * (x * y) := by
    have e1 : x * a * (y * a) = x * y := by
      calc x * a * (y * a) = x * (a * y) * a := by group
        _ = x * (y * a) * a := by rw [comm_of_sq_eq_one hE2 haĒ (hFĒ hy)]
        _ = x * y * (a * a) := by group
        _ = x * y := by rw [hE2 a haĒ, mul_one]
    intro r hr
    rw [← e1]
    calc x * a * (y * a) * r = x * a * ((y * a) * r) := by group
      _ = x * a * (r * (y * a)) := by rw [hya r hr]
      _ = (x * a * r) * (y * a) := by group
      _ = (r * (x * a)) * (y * a) := by rw [hxa r hr]
      _ = r * (x * a * (y * a)) := by group
  refine ⟨x * y, F.mul_mem hx hy, ?_, hxy'⟩
  intro h
  apply hxy
  have hyy : y * y = 1 := hE2 y (hFĒ hy)
  calc x = x * (y * y) := by rw [hyy, mul_one]
    _ = (x * y) * y := (mul_assoc _ _ _).symm
    _ = y := by rw [h, one_mul]

end Index

section Criterion

variable {X : Type} [Group X] [Finite X]


end Criterion

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {E : Subgroup G}

omit [Finite G] in
theorem modOdd_mono {a : G} {K K' : Subgroup G} (h : K ≤ K') : modOdd a K ≤ modOdd a K' := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h hk, rfl⟩


end Frame

end CFSG.ClassicalInvolution.Balance
