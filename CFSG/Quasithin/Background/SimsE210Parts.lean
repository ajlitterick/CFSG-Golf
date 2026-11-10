module

public import CFSG.Quasithin.Vol2.E2TenSix
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SimsE210

open CFSG.Open CFSG.QuasithinUnique

theorem conjSubgroup_eq_conjSub {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    conjSubgroup A g = B6.conjSub g⁻¹ A := by
  ext x
  rw [mem_conjSubgroup_iff, B6.mem_conjSub, inv_inv]


theorem natCard_star_eq_relIndex {Γ : Type} [Group Γ] {M X V : Subgroup Γ} (hVX : V ≤ X) :
    Nat.card (E2.star M X V) = (kerIn M X ⊓ V).relIndex V := by
  have h := Subgroup.relIndex_ker (V.subgroupOf X) (QuotientGroup.mk' ((kerIn M X).subgroupOf X))
  rw [QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hVX] at h
  rw [Subgroup.inf_relIndex_right]
  exact h.symm


end CFSG.Quasithin.SimsE210
