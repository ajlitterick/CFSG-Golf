module

public import CFSG.YGroups.SymmetricGenerators
public import CFSG.YGroups.DoubleCoset

public section

namespace CFSG.YGroups

theorem relIndex_map_range_le {E G : Type*} [Group E] [Group G] [Finite E] (ψ : E →* G)
    (P : Subgroup E) : (P.map ψ).relIndex ψ.range ≤ P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

namespace SymGen.Setup

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω] (S : Setup G E Ω)


end SymGen.Setup

@[expose] def chainStab {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) (j : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | g ∈ S ∧ ∀ m < j, g (β m) = β m}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, fun m hm => ?_⟩
    rw [Equiv.Perm.mul_apply, hb' m hm, ha' m hm]
  one_mem' := ⟨S.one_mem, fun _ _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨S.inv_mem ha, fun m hm => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha' m hm).symm

theorem mem_chainStab {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {β : ℕ → Fin n} {j : ℕ}
    {g : Equiv.Perm (Fin n)} : g ∈ chainStab S β j ↔ g ∈ S ∧ ∀ m < j, g (β m) = β m :=
  Iff.rfl

theorem chainStab_zero {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) :
    chainStab S β 0 = S := by
  ext g
  rw [mem_chainStab]
  exact ⟨fun h => h.1, fun h => ⟨h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩⟩

theorem card_chainStab_step {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) (l : ℕ)
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ chainStab S β l) {o : ℕ}
    (ho : o ≤ (MulAction.orbit K (β l)).ncard) :
    o * Nat.card (chainStab S β (l + 1)) ≤ Nat.card (chainStab S β l) := by
  set Z := chainStab S β l with hZ
  have hsub : (MulAction.orbit K (β l) : Set (Fin n)) ⊆ MulAction.orbit Z (β l) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k.1, hK k.2⟩, rfl⟩
  have h1 : o ≤ (MulAction.orbit Z (β l)).ncard :=
    ho.trans (Set.ncard_le_ncard hsub (Set.toFinite _))
  have h2 : Nat.card (MulAction.orbit Z (β l)) * Nat.card (MulAction.stabilizer Z (β l)) =
      Nat.card Z := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Z (β l))]
  have h3 : Nat.card (MulAction.stabilizer Z (β l)) = Nat.card (chainStab S β (l + 1)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2.1, fun m hm => ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1, fun m hm => g.2.2 m (by omega)⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact g.1.2.2 m h
      · exact MulAction.mem_stabilizer_iff.1 g.2
    · exact g.2.2 l (Nat.lt_succ_self l)
  calc o * Nat.card (chainStab S β (l + 1))
      ≤ (MulAction.orbit Z (β l)).ncard * Nat.card (chainStab S β (l + 1)) :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card (MulAction.orbit Z (β l)) * Nat.card (MulAction.stabilizer Z (β l)) := by
        rw [h3, Nat.card_coe_set_eq]
    _ = Nat.card Z := h2

theorem card_ge_of_chain {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (k : ℕ)
    (β : ℕ → Fin n) (Y : ℕ → Set (Equiv.Perm (Fin n))) (hY : ∀ l < k, Y l ⊆ S)
    (hfix : ∀ l < k, ∀ y ∈ Y l, ∀ m < l, y (β m) = β m) (o : ℕ → ℕ)
    (horb : ∀ l < k, o l ≤ (MulAction.orbit (Subgroup.closure (Y l)) (β l)).ncard) :
    ∏ l ∈ Finset.range k, o l ≤ Nat.card S := by
  have hle : ∀ l < k, Subgroup.closure (Y l) ≤ chainStab S β l := by
    intro l hl
    rw [Subgroup.closure_le]
    intro y hy
    exact ⟨hY l hl hy, hfix l hl y hy⟩
  have key : ∀ j ≤ k, (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) ≤
      Nat.card S := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [chainStab_zero]
      simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ]
      have h1 := ih (by omega)
      have h2 := card_chainStab_step S β j (hle j (by omega)) (horb j (by omega))
      calc (∏ l ∈ Finset.range j, o l) * o j * Nat.card (chainStab S β (j + 1))
          = (∏ l ∈ Finset.range j, o l) * (o j * Nat.card (chainStab S β (j + 1))) := by ring
        _ ≤ (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) :=
          Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card S := h1
  have hpos : 0 < Nat.card (chainStab S β k) := Nat.card_pos
  calc ∏ l ∈ Finset.range k, o l
      ≤ (∏ l ∈ Finset.range k, o l) * Nat.card (chainStab S β k) :=
        Nat.le_mul_of_pos_right _ hpos
    _ ≤ Nat.card S := key k le_rfl

end CFSG.YGroups
