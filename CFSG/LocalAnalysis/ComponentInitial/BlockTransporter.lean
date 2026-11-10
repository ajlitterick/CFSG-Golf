module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

abbrev blockInvolutions (J : Subgroup G) : Set G :=
  {t | orderOf t = 2 ∧ ∃ K ∈ block J, t ∈ centralizer (K : Set G)}


theorem orderOf_inv_mul_mul (g t : G) : orderOf (g⁻¹ * t * g) = orderOf t := by
  rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp, MulEquiv.orderOf_eq]

section Transporter

variable [Finite G] {J : Subgroup G}


theorem mem_normalizer_of_inv_mul_mul_mem (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {t : G} (ht : t ∈ blockInvolutions J) {g : G}
    (hg : g⁻¹ * t * g ∈ blockInvolutions J) : g ∈ normalizer (blockGroup J : Set G) := by
  obtain ⟨ht2, K, hK, htK⟩ := ht
  obtain ⟨-, L, hL, htL⟩ := hg
  have hKcomp : CFSG.Assembly.IsComponentOf K (centralizer ({t} : Set G)) := by
    obtain ⟨a, rfl⟩ := hK.1
    exact isUniversalComponent_conjSub hJ a t htK ht2
  have hLcomp : CFSG.Assembly.IsComponentOf L (centralizer ({g⁻¹ * t * g} : Set G)) := by
    obtain ⟨a, rfl⟩ := hL.1
    exact isUniversalComponent_conjSub hJ a _ htL (by rw [orderOf_inv_mul_mul, ht2])
  have hKg := isComponentOf_map_conj hKcomp g⁻¹
  rw [map_conj_centralizer_singleton, inv_inv, ← conjSub] at hKg
  have hrel : CommRel L (conjSub g⁻¹ K) := isComponentOf_eq_or_commute hLcomp hKg
  have hKgΔ : conjSub g⁻¹ K ∈ block J :=
    ⟨isConjOf_conjSub hK.1 g⁻¹,
      commRel_trans hJ heven mem_block_self.1 hL.1 (isConjOf_conjSub hK.1 g⁻¹) hL.2 hrel⟩
  have := inv_mem (mem_normalizer_blockGroup hJ heven hK hKgΔ)
  rwa [inv_inv] at this


end Transporter

end CFSG.LocalAnalysis.ComponentInitial
