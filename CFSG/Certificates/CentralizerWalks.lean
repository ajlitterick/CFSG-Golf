module

public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.Certificates

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration


theorem conj_eq_of_commute_mul_inv {G : Type*} [Group G] (a g g' : G)
    (h : Commute a (g * g'⁻¹)) : g⁻¹ * a * g = g'⁻¹ * a * g' := by
  have h3 : (g * g'⁻¹)⁻¹ * a * (g * g'⁻¹) = a := by
    have := h.eq
    calc (g * g'⁻¹)⁻¹ * a * (g * g'⁻¹) = (g * g'⁻¹)⁻¹ * (a * (g * g'⁻¹)) := by group
      _ = (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * a) := by rw [this]
      _ = a := by group
  calc g⁻¹ * a * g = g'⁻¹ * ((g * g'⁻¹)⁻¹ * a * (g * g'⁻¹)) * g' := by group
    _ = g'⁻¹ * a * g' := by rw [h3]

end CFSG.Certificates
