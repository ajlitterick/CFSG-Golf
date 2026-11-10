module

public import CFSG.Quasithin.EmptyFaithful.S146A1
public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146Main
public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_sup_eq_oTwoUpper {A B : Subgroup G} (hB : IsPGroup 2 B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : oTwoUpper (A ⊔ B) = oTwoUpper A := by
  refine le_antisymm ?_ (oTwoUpper_mono le_sup_left)
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBA] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hBA hb) (2 ^ j)
  obtain ⟨i, hi⟩ := exists_pow_mem_oTwoUpper A hy'
  refine ⟨j + i, ?_⟩
  rw [pow_add, pow_mul, hpow, hj', mul_one]
  exact hi

omit [Finite G] in
theorem mul_inv_mem_of_relIndex_two {H₀ H : Subgroup G} (h : H₀.relIndex H = 2) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hx0 : x ∉ H₀) (hy0 : y ∉ H₀) : x * y⁻¹ ∈ H₀ := by
  have h2 : (H₀.subgroupOf H).index = 2 := h
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h2
  have key : ∀ z : H, (z : G) ∉ H₀ → z * c ∈ H₀.subgroupOf H := by
    intro z hz
    rcases hc z with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hz
  have h1 := key ⟨x, hx⟩ hx0
  have h2 := key ⟨y, hy⟩ hy0
  have h3 := (H₀.subgroupOf H).mul_mem h1 ((H₀.subgroupOf H).inv_mem h2)
  have e : (⟨x, hx⟩ * c) * (⟨y, hy⟩ * c)⁻¹ = (⟨x, hx⟩ * ⟨y, hy⟩⁻¹ : H) := by group
  rw [e] at h3
  exact Subgroup.mem_subgroupOf.mp h3

omit [Finite G] in
theorem S146A.le_normalizer_of_forall_conj_mem {L K : Subgroup G}
    (h : ∀ g ∈ L, ∀ x ∈ K, g * x * g⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (L.inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem S146A.le_normalizer_of_commutator_le {A B Q : Subgroup G} (hQA : Q ≤ A) (h : ⁅A, B⁆ ≤ Q) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  refine S146A.le_normalizer_of_forall_conj_mem fun b hb x hx => ?_
  have hc : b * x * b⁻¹ = ⁅b, x⁆ * x := by simp only [commutatorElement_def]; group
  have h1 : ⁅x, b⁆ ∈ Q := h (Subgroup.commutator_mem_commutator hx hb)
  have h2 : ⁅b, x⁆ ∈ A := hQA (by
    have := Q.inv_mem h1
    rwa [commutatorElement_inv] at this)
  rw [hc]
  exact A.mul_mem h2 hx

namespace IsDec12

variable {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G]

theorem H₂_le_normalizer_H₁ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₂ ≤ Subgroup.normalizer (H₁ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₁ h.comm

theorem H₁_le_normalizer_H₂ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₂ (by rw [Subgroup.commutator_comm]; exact h.comm)

theorem H₀_le_normalizer_H₁ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₁ : Set G) := by
  rw [h.sup]
  exact sup_le Subgroup.le_normalizer h.H₂_le_normalizer_H₁

theorem H₀_le_normalizer_H₂ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₂ : Set G) := by
  rw [h.sup]
  exact sup_le h.H₁_le_normalizer_H₂ Subgroup.le_normalizer

theorem conjSub_eq_of_not_mem (h : IsDec12 T M H p H₀ H₁ H₂ t) (htH : t ∈ H) {s : G} (hsH : s ∈ H)
    (hs : s ∉ H₀) : conjSub s H₁ = H₂ := by
  have htH₀ : t ∉ H₀ := fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0)
  have hst : s * t⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index hsH htH hs htH₀
  have e : s = (s * t⁻¹) * t := by group
  rw [e, conjSub_mul, ← h.conj]
  exact conjSub_eq_of_mem_normalizer (h.H₀_le_normalizer_H₂ hst)

theorem inf_normalizer_le (h : IsDec12 T M H p H₀ H₁ H₂ t) (hTH : T ≤ H) :
    T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ H₀ := by
  intro s hs
  by_contra hs0
  have hsconj := h.conjSub_eq_of_not_mem (hTH h.t_mem) (hTH hs.1) hs0
  have h1 : conjSub s H₁ = H₁ := conjSub_eq_of_mem_normalizer hs.2
  have h2 : conjSub t H₁ = H₁ := by rw [← h.conj, ← hsconj, h1]
  exact h.t_not (CosetGeom.mem_normalizer_of_conjSub_eq h2)

end IsDec12

end Aux

section Closing

variable {G : Type} [Group G] [Finite G]

@[expose] def Stage14611H2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∀ u : G, u ∈ uHi T M H H₁ → u ∉ quasithinOmegaOneCenter T →
          T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u →
          H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G)) ≤
              centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
            Nonempty (OTwoQuot (H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G))) ≃*
              Equiv.Perm (Fin 3)) ∧
            ¬ H₂ ⊔ (T ⊓ Subgroup.normalizer (H₁ : Set G)) ≤ M


end Closing

end CFSG.Quasithin
