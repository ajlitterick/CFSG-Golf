module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizer of an odd-order rotation subgroup in a dihedral group

In a finite dihedral group, no nontrivial odd-order rotation is centralized
by a reflection.  Hence the centralizer of a nontrivial odd-order rotation
subgroup is contained in the rotation subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u


public theorem mem_sup_zpowers_of_involution_inverts
    {G : Type u} [Group G] {U : Subgroup G} {w : G}
    (_hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) {x : G} :
    x ∈ U ⊔ Subgroup.zpowers w ↔ ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w) := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w)}
        one_mem' := ⟨1, U.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hb with ⟨v, hv, hv_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inl rfl⟩
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inr (by group)⟩
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * v = (u * v⁻¹) * w := by
                calc
                  (u * w) * v = u * (w * v) := by group
                  _ = u * ((w * v * w⁻¹) * w) := by group
                  _ = u * (v⁻¹ * w) := by rw [hwv]
                  _ = (u * v⁻¹) * w := by group
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inr (by rw [hstep])⟩
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * (v * w) = u * v⁻¹ := by
                calc
                  (u * w) * (v * w) = u * (w * v) * w := by group
                  _ = u * ((w * v * w⁻¹) * w) * w := by group
                  _ = u * (v⁻¹ * w) * w := by rw [hwv]
                  _ = u * v⁻¹ := by
                    calc
                      u * (v⁻¹ * w) * w = u * v⁻¹ * (w * w) := by group
                      _ = u * v⁻¹ := by simp [hwsq]
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inl (by rw [hstep])⟩
        inv_mem' := by
          intro a ha
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            exact ⟨u⁻¹, U.inv_mem hu, Or.inl (by simp)⟩
          · rw [heq]
            have hwinvu : w * u⁻¹ * w⁻¹ = u := by
              simpa using hwinv (u⁻¹) (U.inv_mem hu)
            have hstep : (u * w)⁻¹ = u * w := by
              calc
                (u * w)⁻¹ = w⁻¹ * u⁻¹ := by simp
                _ = w * u⁻¹ := by rw [inv_eq_of_mul_eq_one_right hwsq]
                _ = (w * u⁻¹ * w⁻¹) * w := by group
                _ = u * w := by rw [hwinvu]
            exact ⟨u, hu, Or.inr (by rw [hstep])⟩ }
    have hUS : U ≤ S := by
      intro x hx
      exact ⟨x, hx, Or.inl rfl⟩
    have hwS : Subgroup.zpowers w ≤ S := by
      rw [Subgroup.zpowers_le]
      exact ⟨1, U.one_mem, Or.inr (by simp)⟩
    exact (sup_le hUS hwS) hx
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact Subgroup.mem_sup_left hu
    · exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers w)

/-- If a nontrivial odd-order rotation subgroup is centralized by a
dihedral join `U ⊔ ⟨w⟩`, then every centralizer element lies in the rotation
subgroup `U`.  This is the abstract core of the Klein-four attack. -/
public theorem centralizer_odd_rotation_le_U_of_dihedral_join
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hC : Subgroup.centralizer (A : Set G) ≤ U ⊔ Subgroup.zpowers w) :
    Subgroup.centralizer (A : Set G) ≤ U := by
  intro x hx
  have hxD : x ∈ U ⊔ Subgroup.zpowers w := hC hx
  rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp hxD with
    ⟨u, hu, hx_or⟩
  rcases hx_or with hxU | hxuw
  · rw [hxU]
    exact hu
  · exfalso
    let : CommGroup U := IsCyclic.commGroup
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have haA : (a : G) ∈ A := a.2
    have haU : (a : G) ∈ U := hArot haA
    have haodd : Odd (orderOf (a : G)) := hAodd (a : G) haA
    have hcommU : (a : G) * u = u * (a : G) := by
      exact congrArg Subtype.val
        (mul_comm (⟨a, haU⟩ : U) (⟨u, hu⟩ : U))
    have hxcomm : (u * w) * (a : G) = (a : G) * (u * w) := by
      rw [hxuw] at hx
      rw [Subgroup.mem_centralizer_iff] at hx
      exact (hx (a : G) haA).symm
    have hconj_eq_a : (u * w) * (a : G) * (u * w)⁻¹ = (a : G) := by
      calc
        (u * w) * (a : G) * (u * w)⁻¹ =
            (u * w) * (a : G) * (u * w)⁻¹ := rfl
        _ = (a : G) * (u * w) * (u * w)⁻¹ := by rw [hxcomm]
        _ = (a : G) := by group
    have hconj_eq_inv : (u * w) * (a : G) * (u * w)⁻¹ = (a : G)⁻¹ := by
      calc
        (u * w) * (a : G) * (u * w)⁻¹ =
            u * (w * (a : G) * w⁻¹) * u⁻¹ := by group
        _ = u * (a : G)⁻¹ * u⁻¹ := by rw [hwinv (a : G) haU]
        _ = (a : G)⁻¹ := by
          have hcomm : u * (a : G)⁻¹ = (a : G)⁻¹ * u := by
            exact congrArg Subtype.val
              (mul_comm (⟨u, hu⟩ : U) (⟨a, haU⟩ : U)⁻¹)
          rw [hcomm]
          group
    have ha_inv : (a : G) = (a : G)⁻¹ :=
      hconj_eq_a.symm.trans hconj_eq_inv
    have hsq : (a : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [ha_inv]
      simp
    have hord2 : orderOf (a : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hordne : orderOf (a : G) ≠ 1 := by
      intro h
      exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp h))
    have hle : orderOf (a : G) ≤ 2 :=
      Nat.le_of_dvd (by omega) hord2
    have hne2 : orderOf (a : G) ≠ 2 := by
      intro h
      exact haodd.not_two_dvd_nat (by rw [h])
    have hpos : 0 < orderOf (a : G) := orderOf_pos (a : G)
    omega

/-- Bridge from a normalizer-equal-to-dihedral-join hypothesis to the
rotation-subgroup centralizer bound. -/
public theorem centralizer_odd_rotation_le_U_of_normalizer
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w) :
    Subgroup.centralizer (A : Set G) ≤ U :=
  centralizer_odd_rotation_le_U_of_dihedral_join U A w
    hAne hArot hAodd hUcyc hwU hwsq hwinv (by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
        Subgroup.centralizer_le_normalizer (A : Set G) hx
      rw [hN] at hxN
      exact hxN)

/-- No Klein four subgroup centralizes a nontrivial odd-order rotation
subgroup whose normalizer is a dihedral join of a cyclic torus and a
reflection. -/
public theorem no_kleinFour_centralizes_odd_rotation_of_normalizer
    {G : Type u} [Group G] [Finite G]
    (U A V : Subgroup G) (w : G)
    (hAne : A ≠ ⊥) (hArot : A ≤ U)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hUcyc : IsCyclic U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w)
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  have hC_le_U : Subgroup.centralizer (A : Set G) ≤ U :=
    centralizer_odd_rotation_le_U_of_normalizer U A w
      hAne hArot hAodd hUcyc hwU hwsq hwinv hN
  have hVU : V ≤ U := hVleC.trans hC_le_U
  have hVcyc : IsCyclic V := Subgroup.isCyclic_of_le hVU
  have : IsKleinFour V := hVK
  exact IsKleinFour.not_isCyclic hVcyc


end CFSG.GorensteinWalter
