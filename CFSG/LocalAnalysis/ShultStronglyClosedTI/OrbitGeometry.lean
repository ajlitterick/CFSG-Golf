module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]


theorem mem_zpowers_involution_iff {u x : G} (hu : orderOf u = 2) :
    x ∈ Subgroup.zpowers u ↔ x = 1 ∨ x = u := by
  constructor
  · intro hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    · have hcard : Nat.card (Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hu]
      obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers u)).mp hcard
      have hx' : (⟨x, hx⟩ : Subgroup.zpowers u) ≠ 1 :=
        fun h => hxone (congrArg Subtype.val h)
      have hu' : (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) ≠ 1 := by
        intro h
        have hone : u = 1 := congrArg Subtype.val h
        simp [hone] at hu
      exact Or.inr (congrArg Subtype.val ((hw _ hx').trans (hw _ hu').symm))
  · intro h
    rcases h with h | h
    · rw [h]
      exact (Subgroup.zpowers u).one_mem
    · rw [h]
      exact Subgroup.mem_zpowers u


@[expose] def commutingJoinEquiv (E K : Subgroup G) (hdisj : Disjoint E K)
    (hcomm : ∀ e ∈ E, ∀ k ∈ K, Commute e k) : E × K ≃* (E ⊔ K : Subgroup G) := by
  have hcomm' : ∀ (e : E) (k : K), Commute (E.subtype e) (K.subtype k) :=
    fun e k => hcomm e e.property k k.property
  let f := E.subtype.noncommCoprod K.subtype hcomm'
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨E.subtype_injective, K.subtype_injective, by simpa only [Subgroup.range_subtype] using hdisj⟩
  have hrange : f.range = E ⊔ K := by
    exact (MonoidHom.noncommCoprod_range E.subtype K.subtype hcomm').trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)

theorem commutingJoinEquiv_apply (E K : Subgroup G) (hdisj : Disjoint E K)
    (hcomm : ∀ e ∈ E, ∀ k ∈ K, Commute e k) (e : E) (k : K) :
    (commutingJoinEquiv E K hdisj hcomm (e, k) : G) = (e : G) * k := rfl


section NormalizerCosets


end NormalizerCosets

end CFSG.ShultStronglyClosedTI
