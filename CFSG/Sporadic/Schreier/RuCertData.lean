module

public import CFSG.Sporadic.Schreier.RuCheckBasic

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem slotRun_mem {G : Type*} [Group G] {H : Subgroup G} (rows : List SlotRow) {g₁ g₂ : G}
    (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H) : (slotRun rows g₁ g₂).1 ∈ H ∧ (slotRun rows g₁ g₂).2 ∈ H := by
  have hread : ∀ (s : List (ℕ × G)), (∀ p ∈ s, p.2 ∈ H) → ∀ k, slotRead s k ∈ H := by
    intro s hs k
    induction s with
    | nil => exact H.one_mem
    | cons p s ih =>
      obtain ⟨a, g⟩ := p
      by_cases hk : k = a
      · subst hk
        simp only [slotRead, lookup_cons_self, Option.getD_some]
        exact hs _ List.mem_cons_self
      · have := ih fun q hq => hs q (List.mem_cons_of_mem _ hq)
        simpa only [slotRead, lookup_cons_ne hk] using this
  have hfold : ∀ (rows : List SlotRow) (s : List (ℕ × G)), (∀ p ∈ s, p.2 ∈ H) →
      ∀ p ∈ rows.foldl slotStep s, p.2 ∈ H := by
    intro rows
    induction rows with
    | nil => intro s hs; exact hs
    | cons r rows ih =>
      intro s hs
      rw [List.foldl_cons]
      apply ih
      intro p hp
      cases r with
      | mu i j k =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.mul_mem (hread s hs i) (hread s hs j)
        · exact hs p hp
      | iv i j =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.inv_mem (hread s hs i)
        · exact hs p hp
      | pwr e i j =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.pow_mem (hread s hs i) e
        · exact hs p hp
  have h0 : ∀ p ∈ ([(1, g₁), (2, g₂)] : List (ℕ × G)), p.2 ∈ H := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h₁
    · exact h₂
  exact ⟨hread _ (hfold rows _ h0) 1, hread _ (hfold rows _ h0) 2⟩

theorem ruA0_mem : ruA0 ∈ ruP := Subgroup.subset_closure (Set.mem_insert _ _)

theorem ruA1_mem : ruA1 ∈ ruP := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ruC0_mem : ruC0 ∈ ruP := (slotRun_mem ruCProg ruA0_mem ruA1_mem).1

theorem ruC1_mem : ruC1 ∈ ruP := (slotRun_mem ruCProg ruA0_mem ruA1_mem).2

theorem ruN0_mem : ruN0 ∈ ruP := (slotRun_mem ruNProg ruA0_mem ruA1_mem).1

theorem ruN1_mem : ruN1 ∈ ruP := (slotRun_mem ruNProg ruA0_mem ruA1_mem).2

theorem ruZ_mem : ruZ ∈ ruP := ruP.pow_mem ruC0_mem 10

theorem pair_mem {G : Type*} [Group G] {H : Subgroup G} {g₀ g₁ : G} (h₀ : g₀ ∈ H) (h₁ : g₁ ∈ H) :
    ∀ g ∈ [g₀, g₁], g ∈ H := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h₀
  · exact h₁

theorem ruH_mem : ruH ∈ ruP := by
  have hw : ruW ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _
  have hz0 : ruZ0 ∈ ruP := evalSigned_mem (pair_mem ruN0_mem ruN1_mem) _
  exact ruP.mul_mem (ruP.pow_mem (ruP.mul_mem (ruP.mul_mem (ruP.mul_mem hw hz0)
    (ruP.inv_mem hw)) ruZ_mem) 3) hw

theorem ruNs0_mem : ruNs0 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN0_mem) (ruP.inv_mem ruH_mem)

theorem ruNs1_mem : ruNs1 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN1_mem) (ruP.inv_mem ruH_mem)

theorem closure_pair_le {G : Type*} [Group G] {H : Subgroup G} {g₀ g₁ : G} (h₀ : g₀ ∈ H)
    (h₁ : g₁ ∈ H) : Subgroup.closure {g₀, g₁} ≤ H := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact h₀
  · exact h₁

theorem closure_list_le {G : Type*} [Group G] {H : Subgroup G} {l : List G}
    (h : ∀ g ∈ l, g ∈ H) : Subgroup.closure {g | g ∈ l} ≤ H := by
  rw [Subgroup.closure_le]
  exact fun g hg => h g hg

theorem ruC_le : ruC ≤ ruP := closure_pair_le ruC0_mem ruC1_mem

theorem ruN_le : ruN ≤ ruP := closure_pair_le ruNs0_mem ruNs1_mem

theorem ruSGens_mem : ∀ g ∈ ruSGens, g ∈ ruP := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_mem ruNs1_mem) w

theorem ruS_le : ruS ≤ ruP := closure_list_le ruSGens_mem

theorem ruK_le : ruK ≤ ruP := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_mem ruNs1_mem) w

theorem ruJ_le : ruJ ≤ ruP := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruC0_mem ruC1_mem) w


theorem ruE_subset : ruE ⊆ ruP := by
  rintro g (hg | ⟨m, hm, rfl⟩)
  · rw [Set.mem_singleton_iff.1 hg]
    exact ruP.one_mem
  · exact ruP.mul_mem (ruP.mul_mem (ruN_le hm) ruZ_mem) (ruP.inv_mem (ruN_le hm))


end CFSG.Sporadic.RuSchreier
