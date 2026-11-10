module

import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng
public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng
public import CFSG.ClassicalInvolution.Asc77.AscT8T9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T8T

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem exists_triFrame_of_nbrs (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J₁ J₂ : Subgroup G} {z t₁ t₂ : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (h1 : IsUniqueInvolution J₁ t₁) (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (h12 : J₂ ∈ omegaNbr Ω J₁) :
    ∃ R : Fin 3 → Subgroup G, TriFrame Ω ![K, J₁, J₂] ![z, t₁, t₂] R := by
  exact exists_triFrame_of_nbrsE
    (fun hA hB h => T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hA hB h)
    (fun hx hJ hy => T8.mul_comm_of_mem_omegaNbr hp hΩ hx hJ hy)
    (fun hA hR hRA => hΩ.isSylow2In_of_mem_RSet_of_le hp hA hR hRA)
    (fun hc2 hA => mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hA)
    hK hz h1 h2 hJ₁ hJ₂ h12

end Triangle

section Alpha


end Alpha

section Conn


end Conn

end T8T

end CFSG.ClassicalInvolution.Asc77
