module

public import CFSG.ClassicalInvolution.Asc77.AscT8Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Hull

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26_le_sigmaNorm_of_mem_dComp (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) : M ≤ sigmaNorm Ω K := fun _ hx =>
  T8.normalizer_le_sigmaNorm_of_mem hΩ hK hM (Subgroup.le_normalizer hx)


end Hull


end CFSG.ClassicalInvolution.Asc77
