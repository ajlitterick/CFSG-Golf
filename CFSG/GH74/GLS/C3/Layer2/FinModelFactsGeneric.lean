module

public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataBase

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace Facts

theorem mem_sup_zpowers_iff_mul_self {G : Type*} [Group G] (R : Subgroup G) (a : G) (ha : a * a = 1)
    (hn : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (g : G) :
    g ∈ R ⊔ Subgroup.zpowers a ↔ g ∈ R ∨ g * a ∈ R := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let K : Subgroup G :=
    { carrier := {g | g ∈ R ∨ g * a ∈ R}
      one_mem' := Or.inl R.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (R.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact R.mul_mem hx hy
        · right
          have h1 := hn y hy
          have e : x * y * a = (x * a) * (a * y * a⁻¹) := by
            calc x * y * a = x * y * a⁻¹ := by rw [ha']
              _ = x * (a * a) * y * a⁻¹ := by rw [ha, mul_one]
              _ = (x * a) * (a * y * a⁻¹) := by group
          rw [e]
          exact R.mul_mem hx h1
        · left
          have h1 := hn (y * a) hy
          have e : x * y = (x * a) * (a * (y * a) * a⁻¹) := by
            calc x * y = x * (a * a) * y := by rw [ha, mul_one]
              _ = (x * a) * (a * (y * a) * a⁻¹) := by group
          rw [e]
          exact R.mul_mem hx h1
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (R.inv_mem hx)
        · right
          have h1 := hn _ (R.inv_mem hx)
          have e : x⁻¹ * a = a * (x * a)⁻¹ * a⁻¹ := by
            calc x⁻¹ * a = x⁻¹ * a⁻¹ := by rw [ha']
              _ = a * (x * a)⁻¹ * a⁻¹ := by group
          rw [e]
          exact h1 }
  have hK : R ⊔ Subgroup.zpowers a = K := by
    apply le_antisymm
    · apply sup_le
      · intro r hr
        exact Or.inl hr
      · rw [Subgroup.zpowers_le]
        exact Or.inr (by rw [ha]; exact R.one_mem)
    · intro g hg
      rcases hg with hg | hg
      · exact Subgroup.mem_sup_left hg
      · have h1 : g * a ∈ R ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hg
        have h2 : a⁻¹ ∈ R ⊔ Subgroup.zpowers a :=
          Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers a))
        have := mul_mem h1 h2
        simpa using this
  rw [hK]
  exact Iff.rfl

theorem natCard_subgroup_eq_length {m : ℕ} (H : Subgroup (alternatingGroup (Fin m)))
    (L : List (Perm (Fin m))) (hL : L.Nodup)
    (hmem : ∀ z : alternatingGroup (Fin m), z ∈ H ↔ (z : Perm (Fin m)) ∈ L)
    (hlift : ∀ p ∈ L, ∃ z : alternatingGroup (Fin m), (z : Perm (Fin m)) = p) :
    Nat.card H = L.length := by
  classical
  have h1 : Nat.card H = Nat.card (L.toFinset) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun z => ⟨(z.1 : Perm (Fin m)), by simpa using (hmem z.1).1 z.2⟩) ⟨?_, ?_⟩)
    · intro z w h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨p, hp⟩
      obtain ⟨z, hz⟩ := hlift p (by simpa using hp)
      exact ⟨⟨z, (hmem z).2 (by rw [hz]; simpa using hp)⟩, Subtype.ext hz⟩
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]


end Facts

end CFSG.GH74.GLS.C3.Layer2.Model
