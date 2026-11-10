module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic

section CommGraph

variable {G : Type*} [Group G]

@[expose] def commGraph (S : Set (Subgroup G)) : SimpleGraph ↥S :=
  SimpleGraph.fromRel fun K L => K ≠ L ∧ Commutes (K : Subgroup G) (L : Subgroup G)

theorem commGraph_adj {S : Set (Subgroup G)} {K L : ↥S} :
    (commGraph S).Adj K L ↔ K ≠ L ∧ Commutes (K : Subgroup G) (L : Subgroup G) := by
  simp only [commGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h2 | h2⟩
    · exact h2
    · exact ⟨h2.1.symm, h2.2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl ⟨h1, h2⟩⟩


end CommGraph

section WeylConnected

variable {n : ℕ}


end WeylConnected

section PairFamily

variable {n : ℕ} {G : Type*} [Group G]

structure IsPairFamily (L : Pair n → Subgroup G) : Prop where
  inj : Function.Injective L
  commutes_iff : ∀ T T' : Pair n, T ≠ T' → (Commutes (L T) (L T') ↔ Disjoint T.1 T'.1)

variable {L : Pair n → Subgroup G}

@[expose] noncomputable def IsPairFamily.equiv (h : IsPairFamily L) : Pair n ≃ ↥(Set.range L) :=
  Equiv.ofInjective L h.inj


@[expose] noncomputable def IsPairFamily.iso (h : IsPairFamily L) :
    weylGraph n ≃g commGraph (Set.range L) where
  toEquiv := h.equiv
  map_rel_iff' := by
    intro T T'
    rw [commGraph_adj, weylGraph_adj, ne_eq, h.equiv.injective.eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h.commutes_iff T T' h1).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h.commutes_iff T T' h1).mpr h2⟩


end PairFamily

section Swaps

variable {n : ℕ}

abbrev Swaps (n : ℕ) := {t : Equiv.Perm (Fin n) // t.IsSwap}


@[expose] def swapsElt {i j : Fin n} (hij : i ≠ j) : Swaps n :=
  ⟨Equiv.swap i j, i, j, hij, rfl⟩

theorem swap_support_eq_iff {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ({i, j} : Finset (Fin n)) = {k, l}) : Equiv.swap i j = Equiv.swap k l := by
  have hi : i ∈ ({k, l} : Finset (Fin n)) := h ▸ by simp
  have hj : j ∈ ({k, l} : Finset (Fin n)) := h ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · subst hi
    subst hj
    rfl
  · subst hi
    subst hj
    exact Equiv.swap_comm _ _
  · exact absurd (hi.trans hj.symm) hij

@[expose] noncomputable def swapPairEquiv (n : ℕ) : Swaps n ≃ Pair n :=
  Equiv.ofBijective (fun t => ⟨t.1.support, Equiv.Perm.card_support_eq_two.mpr t.2⟩)
    ⟨by
      rintro ⟨s, x, y, hxy, rfl⟩ ⟨t, z, w, hzw, rfl⟩ h
      have h' := congrArg Subtype.val h
      simp only [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzw] at h'
      exact Subtype.ext (swap_support_eq_iff hxy hzw h'),
    by
      rintro ⟨T, hT⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
      exact ⟨swapsElt hxy, Subtype.ext (Equiv.Perm.support_swap hxy)⟩⟩

theorem swapPairEquiv_apply (t : Swaps n) : ((swapPairEquiv n t : Pair n) : Finset (Fin n)) =
    t.1.support := rfl


@[expose] def Swaps.conj (σ : Equiv.Perm (Fin n)) (t : Swaps n) : Swaps n :=
  ⟨σ * t.1 * σ⁻¹, Equiv.Perm.card_support_eq_two.mp (by
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr t.2)⟩


end Swaps

section WeylDatum

variable {n : ℕ} {G : Type*} [Group G] {L : Pair n → Subgroup G}

@[expose] noncomputable def IsPairFamily.swapEquiv (h : IsPairFamily L) :
    ↥(Set.range L) ≃ Swaps n :=
  h.equiv.symm.trans (swapPairEquiv n).symm


end WeylDatum

end CFSG.ClassicalInvolution.Models
