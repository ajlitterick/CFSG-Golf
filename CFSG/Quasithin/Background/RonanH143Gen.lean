module

public import CFSG.Quasithin.Background.RonanH143Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin

theorem exists_labAct {G α : Type*} [Group G] [MulAction G α] {n : ℕ} (X : Fin n → α)
    (hX : Function.Injective X) (H : Subgroup G) (hH : ∀ g ∈ H, ∀ i, ∃ j, g • X i = X j) :
    ∃ π : ↥H →* Equiv.Perm (Fin n), ∀ (g : ↥H) (i : Fin n), X (π g i) = (g : G) • X i := by
  have hc : ∀ g : ↥H, ∀ i, ∃ j, (g : G) • X i = X j := fun g i => hH (g : G) g.2 i
  choose f hf using hc
  have hmul : ∀ g h : ↥H, ∀ i, f (g * h) i = f g (f h i) := by
    intro g h i
    apply hX
    rw [← hf (g * h) i, ← hf g (f h i), ← hf h i, Subgroup.coe_mul, mul_smul]
  have hone : ∀ i, f 1 i = i := by
    intro i
    apply hX
    rw [← hf 1 i, Subgroup.coe_one, one_smul]
  have hinv : ∀ g : ↥H, ∀ i, f g⁻¹ (f g i) = i := by
    intro g i
    apply hX
    rw [← hf g⁻¹ (f g i), ← hf g i, Subgroup.coe_inv, inv_smul_smul]
  have hinv' : ∀ g : ↥H, ∀ i, f g (f g⁻¹ i) = i := by
    intro g i
    apply hX
    rw [← hf g (f g⁻¹ i), ← hf g⁻¹ i, Subgroup.coe_inv, smul_inv_smul]
  refine ⟨{ toFun := fun g =>
              { toFun := f g
                invFun := f g⁻¹
                left_inv := hinv g
                right_inv := hinv' g }
            map_one' := Equiv.ext hone
            map_mul' := fun g h => Equiv.ext (hmul g h) }, fun g i => (hf g i).symm⟩

theorem labAct_eq_of_smul {G α : Type*} [Group G] [MulAction G α] {n : ℕ} (X : Fin n → α)
    (hX : Function.Injective X) (H : Subgroup G) (π : ↥H →* Equiv.Perm (Fin n))
    (hπ : ∀ (g : ↥H) (i : Fin n), X (π g i) = (g : G) • X i) (g : ↥H)
    (σ : Equiv.Perm (Fin n)) (h : ∀ i, (g : G) • X i = X (σ i)) : π g = σ :=
  Equiv.ext fun i => hX ((hπ g i).trans (h i))

theorem card_eq_card_ker_mul {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) :
    Nat.card G = Nat.card π.ker * n.factorial := by
  have h1 := Subgroup.card_ker_mul_card_range π
  rw [hπ, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at h1
  exact h1.symm

theorem ker_eq_of_card_le {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) (N : Subgroup G) (hN : N ≤ π.ker)
    (hc : Nat.card G ≤ Nat.card N * n.factorial) : π.ker = N := by
  have h2 := card_eq_card_ker_mul π hπ
  have hfac : 0 < n.factorial := Nat.factorial_pos n
  rw [h2] at hc
  have hle : Nat.card π.ker ≤ Nat.card N := Nat.le_of_mul_le_mul_right hc hfac
  exact (Subgroup.eq_of_le_of_card_ge hN hle).symm


theorem map_closure_eq_top_of_cycle_swap {G : Type*} [Group G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle)
    (hs : σ.support = ⊤) (x : Fin n) (g₁ g₂ : G) (h1 : π g₁ = σ)
    (h2 : π g₂ = Equiv.swap x (σ x)) : (Subgroup.closure ({g₁, g₂} : Set G)).map π = ⊤ := by
  have hs' : σ.support = Finset.univ := hs.trans Finset.top_eq_univ
  have key := Equiv.Perm.closure_cycle_adjacent_swap hσ hs' x
  rw [MonoidHom.map_closure, Set.image_pair, h1, h2, key]


end CFSG.Quasithin.RonanH143
