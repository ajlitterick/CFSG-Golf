module

public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped Pointwise

section FixedPoints

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem smul_mem_fixedSet_of_mem_centralizer {z g : G} (hg : g ∈ Subgroup.centralizer {z})
    {x : Ω} (hx : z • x = x) : z • g • x = g • x := by
  have hc : z * g = g * z := Subgroup.mem_centralizer_iff.1 hg z rfl
  rw [smul_smul, hc, mul_smul, hx]

theorem smul_fixedSet_of_mem_centralizer {z g : G} (hg : g ∈ Subgroup.centralizer {z}) :
    g • {x : Ω | z • x = x} = {x : Ω | z • x = x} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_fixedSet_of_mem_centralizer hg hy
  · intro hx
    exact ⟨g⁻¹ • x, smul_mem_fixedSet_of_mem_centralizer (inv_mem hg) hx, smul_inv_smul g x⟩

theorem fixed_point_set_orbit_centralizer_bound [Finite G] [Finite Ω] (z : G) (H : Subgroup G)
    (hH : H ≤ Subgroup.centralizer {z})
    (horb : H.index ≤ (Set.range fun g : G => g • {x : Ω | z • x = x}).ncard) :
    H = Subgroup.centralizer {z} ∧
      ∀ g : G, g ∈ Subgroup.centralizer {z} ↔ g • {x : Ω | z • x = x} = {x : Ω | z • x = x} := by
  set Δ : Set Ω := {x | z • x = x} with hΔ
  have hCS : Subgroup.centralizer {z} ≤ MulAction.stabilizer G Δ := fun g hg =>
    MulAction.mem_stabilizer_iff.2 (smul_fixedSet_of_mem_centralizer hg)
  have hHS : H ≤ MulAction.stabilizer G Δ := hH.trans hCS
  have hidx : H.index ≤ (MulAction.stabilizer G Δ).index := by
    rw [MulAction.index_stabilizer]
    exact horb
  have hSH : MulAction.stabilizer G Δ ≤ H := by
    have h1 := Subgroup.relIndex_mul_index hHS
    have hS0 : (MulAction.stabilizer G Δ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hH0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hR1 : H.relIndex (MulAction.stabilizer G Δ) = 1 := by
      rcases Nat.lt_or_ge (H.relIndex (MulAction.stabilizer G Δ)) 2 with h | h
      · rcases Nat.lt_or_ge (H.relIndex (MulAction.stabilizer G Δ)) 1 with h' | h'
        · have h0 : H.relIndex (MulAction.stabilizer G Δ) = 0 := by omega
          rw [h0, zero_mul] at h1
          exact absurd h1.symm hH0
        · omega
      · have : 2 * (MulAction.stabilizer G Δ).index ≤ H.index := by
          rw [← h1]
          exact Nat.mul_le_mul_right _ h
        omega
    exact Subgroup.relIndex_eq_one.1 hR1
  refine ⟨le_antisymm hH (hCS.trans hSH), fun g => ⟨fun hg => hCS hg, fun hg => hH (hSH hg)⟩⟩

end FixedPoints

section Sylow

variable {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)} {p : ℕ}


variable (β : Ω ≃ Sylow p G)


variable {β}


end Sylow

section Involutions

variable {G : Type*} [Group G]

theorem card_centralizer_singleton_map (φ : MulAut G) (y : G) :
    Nat.card (Subgroup.centralizer {φ y}) = Nat.card (Subgroup.centralizer {y}) := by
  rw [← map_centralizer_singleton, Subgroup.card_map_of_injective φ.injective]

theorem involution_class_centralizer_recovery [Finite G] {z : G} (hz : orderOf z = 2) {r : ℕ}
    (x : Fin r → G) (_hx : ∀ i, orderOf (x i) = 2)
    (hcl : ∀ y : G, orderOf y = 2 → IsConj z y ∨ ∃ i, IsConj (x i) y)
    (hcard : ∀ i, Nat.card (Subgroup.centralizer {x i}) < Nat.card (Subgroup.centralizer {z}))
    (α : MulAut G) :
    IsConj z (α z) ∧ ∃ g : G, (Subgroup.centralizer {z}).map α.toMonoidHom =
      (Subgroup.centralizer {z}).map (MulAut.conj g).toMonoidHom := by
  have hαz : orderOf (α z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  rcases hcl (α z) hαz with hconj | ⟨i, hi⟩
  · obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    refine ⟨hconj, g, ?_⟩
    rw [map_centralizer_singleton, map_centralizer_singleton, MulAut.conj_apply, hg]
  · exfalso
    obtain ⟨g, hg⟩ := isConj_iff.1 hi
    have h1 := card_centralizer_singleton_map (MulAut.conj g) (x i)
    rw [MulAut.conj_apply, hg, card_centralizer_singleton_map] at h1
    have := hcard i
    omega

end Involutions

end CFSG.LocalAnalysis.ComponentInitial
