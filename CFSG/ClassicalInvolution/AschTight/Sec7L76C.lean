module

public import CFSG.ClassicalInvolution.AschTight.Sec7L76B
public import CFSG.ClassicalInvolution.AschTight.Sec7Key
public import CFSG.ClassicalInvolution.AschTight.Sec7L76A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem conjSub_iSup_eq_of_forall_mem {η : Set (Subgroup G)} {x : G}
    (h : ∀ U ∈ η, conjSub x U ∈ η) : conjSub x (⨆ U ∈ η, U) = ⨆ U ∈ η, U := by
  refine conjSub_eq_of_le_self ?_
  rw [conjSub_le_iff]
  refine iSup₂_le fun U hU => ?_
  rw [← conjSub_le_iff]
  exact le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) _ (h U hU) le_rfl


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
