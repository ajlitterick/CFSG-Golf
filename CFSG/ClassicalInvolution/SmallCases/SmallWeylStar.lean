module

public import CFSG.ClassicalInvolution.SmallCases.SmallWeylFour

public section

namespace CFSG.ClassicalInvolution.SmallWeyl


section Bridge

variable {A : Type*} [AddCommGroup A]


end Bridge

section Rack

variable {A : Type*} [AddCommGroup A]

theorem Datum.adj_conj_left {p q : Datum A} (h : p.Adj q) : p.Adj (p.conj q) := by
  obtain ⟨h1, h2⟩ := h
  have hp := p.form_vec
  refine ⟨?_, ?_⟩
  · show p.form (q.vec + (if p.pair q = 1 then p.vec else 0)) = 1
    simp only [h1, ↓reduceIte, map_add, hp, add_zero]
    exact h1
  · show (q.form + (if q.pair p = 1 then p.form else 0)) p.vec = 1
    simp only [h2, ↓reduceIte, AddMonoidHom.add_apply, hp, add_zero]
    exact h2

theorem Datum.conj_eq_of_not_pair {p q : Datum A} (h1 : ¬ p.pair q = 1) (h2 : ¬ q.pair p = 1) :
    p.conj q = q :=
  Datum.ext (by simp [Datum.conj, h1]) (by simp [Datum.conj, h2])

theorem exists_component {R : Finset (Datum A)} (hs : IsSymm R) (hc : IsClosed R) {x : Datum A}
    (hx : x ∈ R) :
    ∃ C : Finset (Datum A), C ⊆ R ∧ x ∈ C ∧ IsSymm C ∧ IsClosed C ∧ IsConn C ∧
      ∀ y ∈ R, x.Adj y → y ∈ C := by
  classical
  set C : Finset (Datum A) :=
    R.filter fun y => Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y with hC
  have hmem : ∀ y, y ∈ C ↔
      y ∈ R ∧ Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y :=
    fun y => Finset.mem_filter
  have hxC : x ∈ C := (hmem x).mpr ⟨hx, Relation.ReflTransGen.refl⟩
  refine ⟨C, Finset.filter_subset _ _, hxC, ?_, ?_, ?_, ?_⟩
  · exact fun p hp q hq => hs p ((hmem p).mp hp).1 q ((hmem q).mp hq).1
  · intro p hp q hq
    obtain ⟨hpR, hxp⟩ := (hmem p).mp hp
    obtain ⟨hqR, hxq⟩ := (hmem q).mp hq
    have hr : p.conj q ∈ R := hc p hpR q hqR
    refine (hmem _).mpr ⟨hr, ?_⟩
    have hsym := hs p hpR q hqR
    by_cases hpq : p.pair q = 1
    · have hqp : q.pair p = 1 := hsym.symm.trans hpq
      exact hxp.tail ⟨hpR, hr, Datum.adj_conj_left ⟨hpq, hqp⟩⟩
    · have hqp : ¬ q.pair p = 1 := fun h => hpq (hsym.trans h)
      rw [Datum.conj_eq_of_not_pair hpq hqp]
      exact hxq
  · have key : ∀ y, Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y →
        Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ a.Adj b) x y := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hxb hbc ih =>
        have hbC : b ∈ C := (hmem b).mpr ⟨hbc.1, hxb⟩
        have hcC : c ∈ C := (hmem c).mpr ⟨hbc.2.1, hxb.tail hbc⟩
        exact ih.tail ⟨hbC, hcC, hbc.2.2⟩
    intro p hp q hq
    have : Std.Symm (fun a b : Datum A => a ∈ C ∧ b ∈ C ∧ a.Adj b) :=
      ⟨fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
    exact (Std.Symm.symm _ _ (key p ((hmem p).mp hp).2)).trans (key q ((hmem q).mp hq).2)
  · intro y hy hxy
    exact (hmem y).mpr ⟨hy, Relation.ReflTransGen.single ⟨hx, hy, hxy⟩⟩

theorem rootSet_eq_of_chain_three (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 8)
    {R R₀ : Finset (Datum A)} (hR : R.card = 6) (hsub : R₀ ⊆ R) (hs : IsSymm R₀)
    (hc : IsClosed R₀) {x₀ x₁ x₂ : Datum A} (h₀ : x₀ ∈ R₀) (h₁ : x₁ ∈ R₀) (h₂ : x₂ ∈ R₀)
    (a₀ : x₁.Adj x₀) (a₂ : x₁.Adj x₂) (n : ¬ x₀.Adj x₂) (hne : x₀ ≠ x₂) : R₀ = R := by
  obtain ⟨C, hCR, hxC, hCs, hCc, hCconn, hnb⟩ := exists_component hs hc h₁
  have h0C := hnb x₀ h₀ a₀
  have h2C := hnb x₂ h₂ a₂
  rcases rootSet_classification_three h2 hcard C ⟨x₁, hxC⟩ hCs hCc hCconn with
    h | ⟨-, hadj⟩ | ⟨h6, -⟩
  · exact absurd (Finset.card_le_one.mp h.le x₀ h0C x₂ h2C) hne
  · exact absurd (hadj x₀ h0C x₂ h2C hne) n
  · have hCeq : C = R := Finset.eq_of_subset_of_card_le (hCR.trans hsub) (by omega)
    exact Finset.Subset.antisymm hsub (hCeq ▸ hCR)


end Rack

end CFSG.ClassicalInvolution.SmallWeyl
