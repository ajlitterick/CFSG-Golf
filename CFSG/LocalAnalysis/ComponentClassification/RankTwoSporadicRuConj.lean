module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

section Tree

variable {W : Type*} [Group W]

theorem map_conj_map_conj (E : Subgroup W) (s t : W) :
    (E.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      E.map (MulAut.conj (t * s)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable [Finite W]

theorem forall_of_conjTree {S : Subgroup W} (Wit Mono : Subgroup W → Prop)
    (hWit : ∀ E : Subgroup W, ∀ s ∈ S, Wit (E.map (MulAut.conj s).toMonoidHom) → Wit E)
    (hMono : ∀ E₀ E : Subgroup W, Mono E₀ → E₀ ≤ E → E ≤ S → IsElemAbelian 2 E →
      4 ≤ Nat.card E → Wit E)
    (node : ℕ → Subgroup W) (N : ℕ)
    (hroot : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ i < N, ∃ s ∈ S,
      node i = (zpowers a).map (MulAut.conj s).toMonoidHom)
    (hchild : ∀ i < N, Mono (node i) ∨ ∀ u ∈ S, u ^ 2 = 1 → u ∉ node i →
      (∀ x ∈ node i, x * u = u * x) → ∃ j < N, ∃ s ∈ S,
        node j = (node i ⊔ zpowers u).map (MulAut.conj s).toMonoidHom)
    (hwit : ∀ i < N, 4 ≤ Nat.card (node i) → Mono (node i) ∨ Wit (node i))
    {E : Subgroup W} (hES : E ≤ S) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) : Wit E := by
  have hconj : ∀ s ∈ S, E.map (MulAut.conj s).toMonoidHom ≤ S ∧
      IsElemAbelian 2 (E.map (MulAut.conj s).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj s).toMonoidHom) = Nat.card E := by
    intro s hs
    refine ⟨?_, isElemAbelian_map hE _, card_map_of_injective (MulAut.conj s).injective⟩
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact S.mul_mem (S.mul_mem hs (hES hx)) (S.inv_mem hs)
  have key : ∀ k : ℕ, ∀ i < N, ∀ s ∈ S, node i ≤ E.map (MulAut.conj s).toMonoidHom →
      Nat.card E ≤ Nat.card (node i) + k → Wit E := by
    intro k
    induction k with
    | zero =>
      intro i hi s hs hiE hcard
      obtain ⟨hS', hE', hc'⟩ := hconj s hs
      have heq : node i = E.map (MulAut.conj s).toMonoidHom :=
        eq_of_le_of_card_ge hiE (by omega)
      rcases hwit i hi (by rw [heq, hc']; exact hE4) with hm | hw
      · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
      · exact hWit E s hs (heq ▸ hw)
    | succ k ih =>
      intro i hi s hs hiE hcard
      obtain ⟨hS', hE', hc'⟩ := hconj s hs
      rcases hchild i hi with hm | hch
      · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
      by_cases heq : node i = E.map (MulAut.conj s).toMonoidHom
      · rcases hwit i hi (by rw [heq, hc']; exact hE4) with hm | hw
        · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
        · exact hWit E s hs (heq ▸ hw)
      obtain ⟨u, huE, hui⟩ : ∃ u ∈ E.map (MulAut.conj s).toMonoidHom, u ∉ node i := by
        by_contra hcon
        push Not at hcon
        exact heq (le_antisymm hiE hcon)
      have hcomm : ∀ x ∈ node i, x * u = u * x := fun x hx =>
        congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hiE hx⟩ ⟨u, huE⟩)
      obtain ⟨j, hj, t, ht, hjeq⟩ := hch u (hS' huE) (hE'.2 u huE) hui hcomm
      have hjE : node j ≤ E.map (MulAut.conj (t * s)).toMonoidHom := by
        rw [hjeq, ← map_conj_map_conj]
        exact map_mono (sup_le hiE (zpowers_le.mpr huE))
      have hlt : Nat.card (node i) < Nat.card (node j) := by
        rw [hjeq, card_map_of_injective (MulAut.conj t).injective]
        refine card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hui ?_)
        exact h ▸ mem_sup_right (mem_zpowers u)
      exact ih j hj (t * s) (S.mul_mem ht hs) hjE (by omega)
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx)
    rw [hbot, card_bot] at hE4
    omega
  obtain ⟨i, hi, s, hs, hieq⟩ := hroot a (hES haE) (hE.2 a haE) ha1
  exact key (Nat.card E) i hi s hs (hieq ▸ map_mono (zpowers_le.mpr haE)) (by omega)

end Tree

namespace Cert

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ABGLocalTools
open CFSG.Monster.B.Fischer


section Soundness

variable {n : ℕ}


variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}

theorem witW_of_map_conj {allowPW allowInX allowU : Bool} {E : Subgroup (Equiv.Perm (Fin n))}
    {s : Equiv.Perm (Fin n)} (hs : X.map (MulAut.conj s).toMonoidHom = X)
    (h : WitW X allowPW allowInX allowU (E.map (MulAut.conj s).toMonoidHom)) :
    WitW X allowPW allowInX allowU E := by
  set ι := (MulAut.conj s).toMonoidHom
  have hι : Function.Injective ι := (MulAut.conj s).injective
  rw [← hs] at h
  rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩
  · exact Or.inl ((yWitness_map_iff ι hι X E).mp h)
  · exact Or.inr (Or.inl ⟨h1, (pWitness_map_iff ι hι X E).mp h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, (map_le_map_iff_of_injective hι).mp h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, (uWitness_map_iff ι hι X E).mp h⟩))


end Soundness

section Pair


end Pair

end Cert

end CFSG.ComponentClassification.RankTwoSporadic
