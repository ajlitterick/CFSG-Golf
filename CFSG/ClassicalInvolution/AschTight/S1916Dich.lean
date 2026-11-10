module

public import CFSG.ClassicalInvolution.AschTight.S1911C7b
public import CFSG.ClassicalInvolution.AschTight.S1916Ctx

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_eq_or_of_mem {W D : Subgroup G} {t z x : G}
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (htW : t ∈ W) (ht2 : t * t = 1)
    (hxW : x * t * x⁻¹ ∈ W) (hzD : IsUniqueInvolution D z) (hcD : x * t * x⁻¹ * t⁻¹ ∈ D) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = t * z := by
  set u := x * t * x⁻¹ with hu
  have hut : u * t = t * u := hab _ hxW t htW
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hu2 : u * u = 1 := by
    calc u * u = x * (t * t) * x⁻¹ := by rw [hu]; group
      _ = 1 := by rw [ht2]; group
  have hdd : u * t⁻¹ * (u * t⁻¹) = 1 := by
    calc u * t⁻¹ * (u * t⁻¹) = u * (t * u) * t := by rw [hti]; group
      _ = u * (u * t) * t := by rw [← hut]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu2, ht2, one_mul]
  rcases hzD.unique _ hcD hdd with h | h
  · left
    calc u = u * t⁻¹ * t := by group
      _ = t := by rw [h, one_mul]
  · right
    have h1 : t * u = z := by
      calc t * u = u * t := hut.symm
        _ = u * t⁻¹ := by rw [hti]
        _ = z := h
    calc u = (t * t) * u := by rw [ht2, one_mul]
      _ = t * (t * u) := by group
      _ = t * z := by rw [h1]


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
