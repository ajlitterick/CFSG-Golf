module

public import CFSG.Quasithin.Background.RonanE611Defs
public import CFSG.Quasithin.Background.ONanE68LieBar

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_le {S P L : Subgroup G} (hS : IsSylowTwoOf S L) (hSP : S ≤ P)
    (hPL : P ≤ L) : IsSylowTwoOf S P := by
  refine ⟨hSP, hS.2.1, fun h => hS.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex S P L hSP hPL
  have h2 : (S.subgroupOf P).index = S.relIndex P := rfl
  have h3 : (S.subgroupOf L).index = S.relIndex L := rfl
  rw [h3, ← h1]
  rw [h2] at h
  exact Dvd.dvd.mul_right h _

theorem exists_conj_mem_of_two_element {P S : Subgroup G} (hS : IsSylowTwoOf S P) {y : G}
    (hyP : y ∈ P) (hy : ∃ k : ℕ, y ^ 2 ^ k = 1) : ∃ p ∈ P, p * y * p⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hy
  have hS0 := isSylowTwoOf_subgroupOf_top_of hS
  have hS02 : IsPGroup 2 (S.subgroupOf P) := hS0.2.1
  have hS0i : ¬ 2 ∣ (S.subgroupOf P).index := by
    have := hS0.2.2
    rwa [show ((S.subgroupOf P).subgroupOf (⊤ : Subgroup ↥P)).index = (S.subgroupOf P).index from
      Subgroup.relIndex_top_right _] at this
  let S₀ : Sylow 2 ↥P := hS02.toSylow hS0i
  set yb : ↥P := ⟨y, hyP⟩ with hyb
  have hybk : yb ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hgrp : IsPGroup 2 (Subgroup.zpowers yb) := by
    have hord : orderOf yb ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hybk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := hgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) Q S₀
  have hmem : ∀ z : ↥P, z ∈ Subgroup.zpowers yb → g * z * g⁻¹ ∈ (S₀ : Subgroup ↥P) := by
    intro z hz
    have h1 : z ∈ (Q : Subgroup ↥P) := hQ hz
    have h2 : g * z * g⁻¹ ∈ ((g • Q : Sylow 2 ↥P) : Subgroup ↥P) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
      simpa [mul_assoc] using h1
    rw [hg] at h2
    exact h2
  have h3 := hmem yb (Subgroup.mem_zpowers yb)
  refine ⟨(g : G), g.2, ?_⟩
  have h4 : (g * yb * g⁻¹ : ↥P) ∈ S.subgroupOf P := h3
  exact h4

end Sylow

section RootGroup

variable {Y : Type} [Group Y] [Finite Y]

theorem le_rootGroupOfParabolicR {P S W : Subgroup Y} (hS : IsSylowTwoOf S P) (hWS : W ≤ S)
    (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w) (hWn : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W)
    (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1) : W ≤ rootGroupOfParabolicR P := by
  intro w hw
  refine Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨hS.1 (hWS hw), hW2 w hw⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have key : y * w = w * y := by
    refine Subgroup.closure_induction (p := fun y _ => y * w = w * y) ?_ ?_ ?_ ?_ hy
    · intro x hx
      obtain ⟨hxP, hx2⟩ := hx
      obtain ⟨p, hp, hpx⟩ := exists_conj_mem_of_two_element hS hxP hx2
      have hw' : p * w * p⁻¹ ∈ W := hWn p hp w hw
      have h1 := hWc _ hw' _ hpx
      have h2 : p * (w * x) * p⁻¹ = p * (x * w) * p⁻¹ := by
        have e1 : p * (w * x) * p⁻¹ = (p * w * p⁻¹) * (p * x * p⁻¹) := by group
        have e2 : p * (x * w) * p⁻¹ = (p * x * p⁻¹) * (p * w * p⁻¹) := by group
        rw [e1, e2]
        exact h1
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    · simp
    · intro a b _ _ ha hb
      calc a * b * w = a * (b * w) := by rw [mul_assoc]
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by rw [mul_assoc]
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by rw [mul_assoc]
    · intro a _ ha
      calc a⁻¹ * w = a⁻¹ * w * a * a⁻¹ := by group
        _ = a⁻¹ * (w * a) * a⁻¹ := by rw [mul_assoc a⁻¹ w a]
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [← ha]
        _ = w * a⁻¹ := by group
  exact key

end RootGroup

section OddIndex


end OddIndex

end CFSG.Quasithin.RonanE611
