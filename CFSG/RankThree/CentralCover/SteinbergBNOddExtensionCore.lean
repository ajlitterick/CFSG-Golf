module

public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.CentralCover

open scoped commutatorElement

section CentralCommutators

variable {P : Type*} [Group P] {A : Subgroup P}

theorem mul_comm_of_mem_le_center (hA : A ≤ Subgroup.center P) {a : P} (ha : a ∈ A) (g : P) :
    a * g = g * a :=
  (Subgroup.mem_center_iff.1 (hA ha) g).symm

theorem commutatorElement_mul_central_left (hA : A ≤ Subgroup.center P) {a : P} (ha : a ∈ A)
    (x y : P) : ⁅x * a, y⁆ = ⁅x, y⁆ := by
  have h1 := mul_comm_of_mem_le_center hA ha
  calc ⁅x * a, y⁆ = x * (a * y) * a⁻¹ * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * (y * a) * a⁻¹ * x⁻¹ * y⁻¹ := by rw [h1 y]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_central_right (hA : A ≤ Subgroup.center P) {c : P} (hc : c ∈ A)
    (x y : P) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h1 := mul_comm_of_mem_le_center hA hc
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹) * c⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * c) * c⁻¹ * y⁻¹ := by rw [h1 x⁻¹]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

variable (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A)
include hA hcomm


variable {p : ℕ} (hpow : ∀ x : P, x ^ p ∈ A)
include hpow


end CentralCommutators

section AbelianPower

variable {P : Type*} [Group P] {A : Subgroup P} (hA : A ≤ Subgroup.center P)
include hA


end AbelianPower


theorem card_inf_ker_mul_card_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H : Subgroup G) : Nat.card (H ⊓ f.ker : Subgroup G) * Nat.card (H.map f) = Nat.card H := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
    ← Subgroup.inf_subgroupOf_left] at h
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ f.ker ≤ H)).toEquiv]
  exact h

section RankFormula

variable {P : Type*} [Group P] {A : Subgroup P} [A.Normal] {p : ℕ}


variable (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A)
  (hpow : ∀ x : P, x ^ p ∈ A) (hp : p.Prime) (hp2 : p ≠ 2)
include hA hcomm hpow hp hp2


end RankFormula


section QuotientCounting

variable {W : Type*} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
  (hWc : ∀ u v : W, u * v = v * u) (hWp : ∀ u : W, u ^ p = 1)
include hp hWc hWp

theorem card_sup_zpowers_of_not_mem {U : Subgroup W} {g : W} (hg : g ∉ U) :
    Nat.card (U ⊔ Subgroup.zpowers g : Subgroup W) = p * Nat.card U := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU : U.Normal := ⟨fun n hn x => by rw [hWc x n, mul_inv_cancel_right]; exact hn⟩
  have hg1 : g ≠ 1 := fun h => hg (h ▸ U.one_mem)
  have hgo : orderOf g = p := orderOf_eq_prime (hWp g) hg1
  set H := U ⊔ Subgroup.zpowers g
  have hle : Nat.card H ≤ Nat.card U * p := by
    have hsurj : Function.Surjective
        (fun x : U × Fin p => (⟨x.1 * g ^ (x.2 : ℕ), Subgroup.mul_mem _
          (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right
            (Subgroup.npow_mem_zpowers g _))⟩ : H)) := by
      rintro ⟨x, hx⟩
      obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      have hz' := (mem_zpowers_iff_mem_range_orderOf (x := g) (y := z)).1 hz
      rw [hgo] at hz'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz'
      exact ⟨(⟨u, hu⟩, ⟨k, Finset.mem_range.1 hk⟩), rfl⟩
    have h := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_fin] at h
  have hW : IsPGroup p W := fun x => ⟨1, by rw [pow_one]; exact hWp x⟩
  obtain ⟨a, ha⟩ := (hW.to_subgroup H).exists_card_eq
  obtain ⟨b, hb⟩ := (hW.to_subgroup U).exists_card_eq
  have hne : Nat.card H ≠ Nat.card U := fun h => hg (by
    rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ H) h.le]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
    (by rw [← ha, ← hb]; exact Subgroup.card_dvd_of_le le_sup_left)
  have hba' : b + 1 ≤ a := lt_of_le_of_ne hba (fun h => hne (by rw [ha, hb, h]))
  have h1 : p ^ (b + 1) ≤ p ^ a := Nat.pow_le_pow_right hp.pos hba'
  rw [ha, hb] at hle ⊢
  rw [pow_succ] at h1
  rw [mul_comm]
  exact le_antisymm hle h1

end QuotientCounting

section Orthogonal


end Orthogonal


end CFSG.RankThree.CentralCover
