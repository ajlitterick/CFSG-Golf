module

public import CFSG.Quasithin.AppendixH.H14.M24InvolutionClasses
public import CFSG.Quasithin.Background.F7TwoInvSporM23
public import CFSG.Quasithin.Background.F7TwoInvSporM22

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Quasithin.F7Two


theorem m22_involutions_conj
    (u u' : ↥NativeSporadic.M22) (hu : orderOf u = 2) (hu' : orderOf u' = 2) :
    ∃ c : ↥NativeSporadic.M22, u' = c * u * c⁻¹ := by
  obtain ⟨c₁, hc₁, h₁⟩ :=
    m22_inner_cover u.2 (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨c₂, hc₂, h₂⟩ :=
    m22_inner_cover u'.2 (by rw [Subgroup.orderOf_coe, hu'])
  refine ⟨⟨c₂ * c₁⁻¹, Subgroup.mul_mem _ hc₂ (Subgroup.inv_mem _ hc₁)⟩, ?_⟩
  apply Subtype.ext
  show (u' : Equiv.Perm (Fin 22)) =
    (c₂ * c₁⁻¹) * (u : Equiv.Perm (Fin 22)) * (c₂ * c₁⁻¹)⁻¹
  rw [h₁, h₂]
  group


section Certs


end Certs

end CFSG.Quasithin.AppendixH.H14
