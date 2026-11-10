module

public import CFSG.GH74.GLS.IVK.L2.TShape
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.Semidihedral

section Lemma19Basics

variable {H : Type} [Group H] (Khat : Subgroup H) [Khat.Normal] {F : Type} [Field F]

theorem exists_z (hC : centralizer (Khat : Set H) ≤ Khat)
    (φ : ↥Khat ≃* Matrix.SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0) :
    ∃ z : H, z ∈ Khat ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ x ∈ Khat, x * x = 1 → x = 1 ∨ x = z) ∧
      (∀ h : H, h * z = z * h) ∧ (∀ g ∈ center H, g = 1 ∨ g = z) := by
  set z₀ : ↥Khat := φ.symm (OddFieldSL2.minusIdentity F) with hz₀
  have hφz : φ z₀ = OddFieldSL2.minusIdentity F := φ.apply_symm_apply _
  have hz1 : z₀ ≠ 1 := by
    intro h
    have := OddFieldSL2.minusIdentity_ne_one F h2
    apply this
    rw [← hφz, h, map_one]
  have hzz : z₀ * z₀ = 1 := by
    apply φ.injective
    rw [map_mul, hφz, map_one, ← pow_two]
    exact OddFieldSL2.minusIdentity_square F
  have huniq : ∀ x ∈ Khat, x * x = 1 → x = 1 ∨ x = (z₀ : H) := by
    intro x hx hx2
    have hinv : (φ ⟨x, hx⟩)⁻¹ = φ ⟨x, hx⟩ := by
      rw [← map_inv]
      congr 1
      apply Subtype.ext
      exact inv_eq_of_mul_eq_one_right hx2
    rcases OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 _ hinv with h1 | h1
    · left
      have : (⟨x, hx⟩ : ↥Khat) = 1 := φ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥Khat) = z₀ := φ.injective (by rw [h1, hφz])
      exact congrArg Subtype.val this
  have hcentral : ∀ h : H, h * (z₀ : H) = (z₀ : H) * h := by
    intro h
    have hmem : h * (z₀ : H) * h⁻¹ ∈ Khat := Subgroup.Normal.conj_mem ‹Khat.Normal› _ z₀.2 h
    have hsq : (h * (z₀ : H) * h⁻¹) * (h * (z₀ : H) * h⁻¹) = 1 := by
      calc (h * (z₀ : H) * h⁻¹) * (h * (z₀ : H) * h⁻¹) = h * ((z₀ : H) * (z₀ : H)) * h⁻¹ := by
            group
        _ = 1 := by
          have : (z₀ : H) * (z₀ : H) = 1 := congrArg Subtype.val hzz
          rw [this]; group
    rcases huniq _ hmem hsq with h1 | h1
    · exfalso
      apply hz1
      apply Subtype.ext
      have : (z₀ : H) = h⁻¹ * (h * (z₀ : H) * h⁻¹) * h := by group
      rw [this, h1]
      simp
    · calc h * (z₀ : H) = (h * (z₀ : H) * h⁻¹) * h := by group
        _ = (z₀ : H) * h := by rw [h1]
  have hcenter : ∀ g ∈ center H, g = 1 ∨ g = (z₀ : H) := by
    intro g hg
    have hgC : g ∈ centralizer (Khat : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact (Subgroup.mem_center_iff.mp hg k)
    have hgK : g ∈ Khat := hC hgC
    have hcen : φ ⟨g, hgK⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨k, rfl⟩ := φ.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hg k
    rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).1 hcen with h1 | h1
    · left
      have : (⟨g, hgK⟩ : ↥Khat) = 1 := φ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨g, hgK⟩ : ↥Khat) = z₀ := φ.injective (by
        rw [h1, hφz, ProjectiveSL2Cover.minusIdentity_eq_neg_one]; rfl)
      exact congrArg Subtype.val this
  exact ⟨z₀, z₀.2, fun h => hz1 (Subtype.ext h), congrArg Subtype.val hzz, huniq, hcentral, hcenter⟩

end Lemma19Basics

section Lemma19c

theorem zpowers_normal_of_central {G : Type*} [Group G] {z : G} (hz : ∀ g, g * z = z * g) :
    (Subgroup.zpowers z).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h0 : g * z * g⁻¹ = z := by
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hz g]
        _ = z := by group
    have h1 : g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := (conj_zpow).symm
    rw [h1, h0]
    exact Subgroup.zpow_mem_zpowers z k⟩

theorem mul_comm_of_mem_zpowers_sup {G : Type*} [Group G] {q₀ z : G} (hz : ∀ g, g * z = z * g)
    {x y : G} (hx : x ∈ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z)
    (hy : y ∈ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) : x * y = y * x := by
  have hzn : (Subgroup.zpowers z).Normal := zpowers_normal_of_central hz
  rw [Subgroup.mem_sup_of_normal_right] at hx hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx₁
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₁
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx₂
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₂
  have h1 : Commute q₀ z := hz q₀
  have hAC : Commute (q₀ ^ i) (q₀ ^ j) := Commute.zpow_zpow_self q₀ i j
  have hAD : Commute (q₀ ^ i) (z ^ l) := Commute.zpow_zpow h1 i l
  have hBC : Commute (z ^ k) (q₀ ^ j) := Commute.zpow_zpow h1.symm k j
  have hBD : Commute (z ^ k) (z ^ l) := Commute.zpow_zpow_self z k l
  exact Commute.mul_left (Commute.mul_right hAC hAD) (Commute.mul_right hBC hBD)


end Lemma19c

end CFSG.GH74.GLS.IVK
