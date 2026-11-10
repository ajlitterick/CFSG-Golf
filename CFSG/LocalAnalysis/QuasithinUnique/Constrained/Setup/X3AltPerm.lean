module

public import Certificates.Certificate4138

public section

set_option maxRecDepth 100000

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv CFSG.QuasithinUnique

section Generic


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem top_of_adjacent_swaps {m : ℕ} {G : Subgroup (Perm (Fin (m + 1)))}
    (h : ∀ i : Fin m, swap i.castSucc i.succ ∈ G) : G = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ m]
    trivial
  refine (Submonoid.closure_le (S := G.toSubmonoid)).mpr ?_ hσ
  rintro _ ⟨i, rfl⟩
  exact h i

omit [Fintype α] in
theorem swap_apply_mem_of_mem {G : Subgroup (Perm α)} {σ : Perm α} (hσ : σ ∈ G) {a b : α}
    (h : swap a b ∈ G) : swap (σ a) (σ b) ∈ G := by
  rw [swap_apply_apply]
  exact G.mul_mem (G.mul_mem hσ h) (G.inv_mem hσ)

theorem card_eq_two_mul_card_inf_alt {K : Subgroup (Perm α)} {s : Perm α} (hsK : s ∈ K)
    (hs : Perm.sign s = -1) : Nat.card K = 2 * Nat.card ↥(K ⊓ alternatingGroup α) := by
  have h2 : (alternatingGroup α).relIndex K = 2 := by
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨s, hsK, fun b hb => ?_⟩
    rcases Int.units_eq_one_or (Perm.sign b) with h1 | h1
    · refine Or.inr ⟨Perm.mem_alternatingGroup.mpr h1, fun hmem => ?_⟩
      rw [Perm.mem_alternatingGroup, map_mul, h1, hs] at hmem
      exact absurd hmem (by decide)
    · refine Or.inl ⟨?_, fun hmem => ?_⟩
      · rw [Perm.mem_alternatingGroup, map_mul, h1, hs]
        rfl
      · rw [Perm.mem_alternatingGroup, h1] at hmem
        exact absurd hmem (by decide)
  have h3 := Subgroup.relIndex_mul_card (alternatingGroup α) K
  rw [h2, inf_comm] at h3
  omega

end Generic

section Case

variable {n : ℕ}

theorem two_gen_perm_case (h5 : 5 ≤ n) (X Y : Subgroup (Perm (Fin n))) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsX : swap a b ∈ X) (hsY : swap a b ∈ Y) (hcX : swap a b * swap a c ∈ X)
    (hXYtop : X ⊔ Y = ⊤)
    {xS yS xA yA : Perm (Fin n)} (hxS : xS ∉ X) (hyS : yS ∉ Y)
    (hxA : xA ∈ alternatingGroup (Fin n)) (hxA' : xA ∉ X)
    (hyA : yA ∈ alternatingGroup (Fin n)) (hyA' : yA ∉ Y)
    {m q : ℕ} (hcard : Nat.card ↥(X ⊓ Y) = m) (hfac : n.factorial = m * q) (hq : ¬ 2 ∣ q)
    {D R : Subgroup (Perm (Fin n))} (hD : D = ⊤ ∨ D = alternatingGroup (Fin n))
    (hR : IsSylowTwoOf R D) :
    ∃ X' Y' : Subgroup (Perm (Fin n)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧ X' ⊔ Y' = D := by
  have hsgn : Perm.sign (swap a b) = -1 := Perm.sign_swap hab
  have hcardn : Nat.card (Perm (Fin n)) = n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmpos : 0 < m := by
    rw [← hcard]
    exact Nat.card_pos
  rcases hD with rfl | rfl
  · refine hasTwoGen_of_odd_index ?_ ?_ hXYtop ?_ hR
    · exact lt_top_iff_ne_top.mpr fun h => hxS (h ▸ Subgroup.mem_top xS)
    · exact lt_top_iff_ne_top.mpr fun h => hyS (h ▸ Subgroup.mem_top yS)
    · rw [Subgroup.relIndex_top_right]
      have h1 := Subgroup.card_mul_index (X ⊓ Y)
      rw [hcard, hcardn, hfac] at h1
      have h2 : (X ⊓ Y).index = q := Nat.eq_of_mul_eq_mul_left hmpos h1
      rwa [h2]
  · have hα : 5 ≤ Nat.card (Fin n) := by simpa using h5
    have hf3 : (swap a b * swap a c).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    have hgenA : (X ⊓ alternatingGroup (Fin n)) ⊔ (Y ⊓ alternatingGroup (Fin n)) =
        alternatingGroup (Fin n) :=
      le_antisymm (sup_le inf_le_right inf_le_right)
        (alt_le_sup_of_common_odd hsX hsY hsgn hXYtop hα hf3 hcX)
    refine hasTwoGen_of_odd_index ?_ ?_ hgenA ?_ hR
    · refine lt_of_le_of_ne inf_le_right fun h => hxA' ?_
      have : xA ∈ X ⊓ alternatingGroup (Fin n) := by rw [h]; exact hxA
      exact this.1
    · refine lt_of_le_of_ne inf_le_right fun h => hyA' ?_
      have : yA ∈ Y ⊓ alternatingGroup (Fin n) := by rw [h]; exact hyA
      exact this.1
    · have hK : (X ⊓ alternatingGroup (Fin n)) ⊓ (Y ⊓ alternatingGroup (Fin n)) =
          (X ⊓ Y) ⊓ alternatingGroup (Fin n) := by
        ext x
        simp only [Subgroup.mem_inf]
        tauto
      rw [hK]
      have hle : (X ⊓ Y) ⊓ alternatingGroup (Fin n) ≤ alternatingGroup (Fin n) := inf_le_right
      have hm2 := card_eq_two_mul_card_inf_alt (K := X ⊓ Y) (s := swap a b) ⟨hsX, hsY⟩ hsgn
      have hKpos : 0 < Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) := Nat.card_pos
      have h1 := Subgroup.relIndex_mul_card ((X ⊓ Y) ⊓ alternatingGroup (Fin n))
        (alternatingGroup (Fin n))
      rw [inf_eq_left.mpr hle] at h1
      have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h2 := Subgroup.card_mul_index (alternatingGroup (Fin n))
      rw [hcardn, alternatingGroup.index_eq_two] at h2
      rw [hcard] at hm2
      have h3 : Nat.card ↥(alternatingGroup (Fin n)) =
          Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) * q := by
        have : 2 * Nat.card ↥(alternatingGroup (Fin n)) =
            2 * (Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) * q) := by
          rw [mul_comm, h2, hfac, hm2]
          ring
        omega
      rw [h3, mul_comm] at h1
      have h4 : ((X ⊓ Y) ⊓ alternatingGroup (Fin n)).relIndex (alternatingGroup (Fin n)) = q :=
        Nat.eq_of_mul_eq_mul_left hKpos h1
      rwa [h4]

end Case


theorem mem_alt_swap_mul_swap {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) : swap a b * swap c d ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  rfl


section Case6

@[expose] def blkX6 (i : Fin 6) : ℕ := if i.val < 4 then 0 else 1

@[expose] def blkY6 (i : Fin 6) : ℕ := i.val / 2

theorem sup6 : relStab blkX6 ⊔ relStab blkY6 = ⊤ := by
  refine top_of_adjacent_swaps (m := 5) fun i => ?_
  have h01 : swap (0 : Fin 6) 1 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h12 : swap (1 : Fin 6) 2 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h23 : swap (2 : Fin 6) 3 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h45 : swap (4 : Fin 6) 5 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h13 : swap (1 : Fin 6) 3 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have hy : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_right (by decide +kernel)
  have h14 : swap (1 : Fin 6) 4 ∈ relStab blkX6 ⊔ relStab blkY6 := by
    have h := swap_apply_mem_of_mem hy h12
    have e1 : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) 1 = 1 := by decide
    have e2 : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) 2 = 4 := by decide
    rwa [e1, e2] at h
  have h34 : swap (3 : Fin 6) 4 ∈ relStab blkX6 ⊔ relStab blkY6 := by
    have h := swap_apply_mem_of_mem h13 h14
    have e1 : (swap (1 : Fin 6) 3 : Perm (Fin 6)) 1 = 3 := by decide
    have e2 : (swap (1 : Fin 6) 3 : Perm (Fin 6)) 4 = 4 := by decide
    rwa [e1, e2] at h
  fin_cases i
  exacts [h01, h12, h23, h34, h45]

theorem card6 : Nat.card ↥(relStab blkX6 ⊓ relStab blkY6) = 16 := by
  have h : Fintype.card
      {σ : Perm (Fin 6) // σ ∈ relStab blkX6 ∧ σ ∈ relStab blkY6} = 16 := by
    decide +kernel
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ => Subgroup.mem_inf),
    Nat.card_eq_fintype_card]
  exact h

theorem two_gen_6 {D R : Subgroup (Perm (Fin 6))}
    (hD : D = ⊤ ∨ D = alternatingGroup (Fin 6)) (hR : IsSylowTwoOf R D) :
    ∃ X' Y' : Subgroup (Perm (Fin 6)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧ X' ⊔ Y' = D :=
  two_gen_perm_case (by norm_num) (relStab blkX6) (relStab blkY6) 0 1 2
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) sup6
    (xS := swap 0 4) (yS := swap 1 2) (xA := swap 0 4 * swap 1 5) (yA := swap 1 2 * swap 3 4)
    (by decide +kernel) (by decide +kernel)
    (mem_alt_swap_mul_swap (by decide) (by decide)) (by decide +kernel)
    (mem_alt_swap_mul_swap (by decide) (by decide)) (by decide +kernel) card6
    (q := 45) (by decide +kernel) (by decide +kernel) hD hR

end Case6

section Case7


end Case7

section Case8


end Case8

section Abstract

variable {Γ Γ' : Type*} [Group Γ] [Group Γ']


@[expose] def TwoGenPerm (n : ℕ) : Prop :=
  ∀ {D R : Subgroup (Perm (Fin n))}, (D = ⊤ ∨ D = alternatingGroup (Fin n)) →
    IsSylowTwoOf R D → ∃ X' Y' : Subgroup (Perm (Fin n)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧
      X' ⊔ Y' = D

theorem twoGenPerm_six : TwoGenPerm 6 := fun hD hR => two_gen_6 hD hR


end Abstract

end CFSG.QuasithinUnique.Setup.X3
