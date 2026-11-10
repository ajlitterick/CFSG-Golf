module

public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Vol2.Ch3E213MKer

public section

namespace CFSG.Quasithin.SimsE2

namespace Dih

theorem dParam_dvd_of_dvd {q m : ℕ} (h : q ∣ 2 ^ m - 1) : E2.dParam q ∣ m := by
  unfold E2.dParam
  apply orderOf_dvd_of_pow_eq_one
  have h1 : ((2 ^ m - 1 : ℕ) : ZMod q) = 0 := (CharP.cast_eq_zero_iff (ZMod q) q _).2 h
  rw [Nat.cast_sub Nat.one_le_two_pow] at h1
  push_cast at h1
  exact sub_eq_zero.1 h1


variable {N : Type*} [Group N]

@[expose] def fixSub (σ : MulAut N) : Subgroup N where
  carrier := {x | σ x = x}
  mul_mem' {x y} hx hy := by
    have hx' : σ x = x := hx
    have hy' : σ y = y := hy
    change σ (x * y) = x * y
    rw [map_mul, hx', hy']
  one_mem' := map_one σ
  inv_mem' {x} hx := by
    have hx' : σ x = x := hx
    change σ x⁻¹ = x⁻¹
    rw [map_inv, hx']

theorem mem_fixSub {σ : MulAut N} {x : N} : x ∈ fixSub σ ↔ σ x = x := Iff.rfl

@[expose] def commHom (hc : ∀ x y : N, x * y = y * x) (σ : MulAut N) : N →* N where
  toFun x := x⁻¹ * σ x
  map_one' := by rw [inv_one, map_one, one_mul]
  map_mul' x y := by
    change (x * y)⁻¹ * σ (x * y) = x⁻¹ * σ x * (y⁻¹ * σ y)
    calc (x * y)⁻¹ * σ (x * y) = x⁻¹ * (y⁻¹ * σ x) * σ y := by
          rw [map_mul, mul_inv_rev, hc y⁻¹ x⁻¹]
          simp only [mul_assoc]
      _ = x⁻¹ * σ x * (y⁻¹ * σ y) := by
          rw [hc y⁻¹ (σ x)]
          simp only [mul_assoc]

theorem commHom_apply (hc : ∀ x y : N, x * y = y * x) (σ : MulAut N) (x : N) :
    commHom hc σ x = x⁻¹ * σ x := rfl

theorem card_le_sq_card_fixSub [Finite N] (hc : ∀ x y : N, x * y = y * x)
    (hsq : ∀ x : N, x * x = 1) {s : MulAut N} (hs : s * s = 1) {U : Subgroup N}
    (hU : ∀ u ∈ U, s u ∈ U) : Nat.card U ≤ Nat.card ↥(U ⊓ fixSub s) ^ 2 := by
  set φ : ↥U →* N := (commHom hc s).comp U.subtype with hφ
  have hss : ∀ x : N, s (s x) = x := fun x => by
    rw [← MulAut.mul_apply, hs, MulAut.one_apply]
  have hinv : ∀ x : N, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hker : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ fixSub s) := by
    rw [← Subgroup.card_map_of_injective (K := φ.ker) U.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : N)⁻¹ * s u = 1 := hu
    exact ⟨u.2, (inv_mul_eq_one.1 hu').symm⟩
  have hrange : Nat.card φ.range ≤ Nat.card ↥(U ⊓ fixSub s) := by
    apply Subgroup.card_le_of_le
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hy
    have e : φ u = (u : N)⁻¹ * s u := rfl
    rw [e]
    refine ⟨U.mul_mem (U.inv_mem u.2) (hU u u.2), ?_⟩
    show s ((u : N)⁻¹ * s u) = (u : N)⁻¹ * s u
    rw [map_mul, map_inv, hss, hinv (s u), hinv (u : N)]
    exact hc _ _
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card U := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index φ.ker
  calc Nat.card U = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ Nat.card ↥(U ⊓ fixSub s) * Nat.card ↥(U ⊓ fixSub s) := Nat.mul_le_mul hker hrange
    _ = Nat.card ↥(U ⊓ fixSub s) ^ 2 := (sq _).symm

theorem card_mul_card_le {H K U : Subgroup N} [Finite U] (hHU : H ≤ U) (hKU : K ≤ U)
    (hHK : H ⊓ K = ⊥) : Nat.card H * Nat.card K ≤ Nat.card U := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x : ↥H × ↥K => (⟨(x.1 : N) * x.2, U.mul_mem (hHU x.1.2) (hKU x.2.2)⟩ : U)) ?_
  rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
  have heq' : (h₁ : N) * k₁ = h₂ * k₂ := congrArg Subtype.val heq
  have hmem : (h₂ : N)⁻¹ * h₁ ∈ H ⊓ K := by
    refine ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, ?_⟩
    have e : (h₂ : N)⁻¹ * h₁ = k₂ * (k₁ : N)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
    rw [e]
    exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
  rw [hHK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hk : (k₁ : N) = k₂ := by
    rw [hmem] at heq'
    exact mul_left_cancel heq'
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hk)

theorem pow_apply_mem {γ : MulAut N} {U : Subgroup N} (hU : ∀ u ∈ U, γ u ∈ U) (n : ℕ) :
    ∀ u ∈ U, (γ ^ n) u ∈ U := by
  induction n with
  | zero => intro u hu; simpa using hu
  | succ n ih =>
    intro u hu
    rw [pow_succ', MulAut.mul_apply]
    exact hU _ (ih u hu)

theorem pow_apply_eq {γ : MulAut N} {x : N} (hx : γ x = x) (n : ℕ) : (γ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hx]

theorem dvd_card_sub_one [Finite N] {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) {γ : MulAut N}
    (hγ : orderOf γ = p ^ a) {U : Subgroup N} (hU : ∀ u ∈ U, γ u ∈ U)
    (hfree : U ⊓ fixSub (γ ^ p ^ (a - 1)) = ⊥) : p ^ a ∣ Nat.card U - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hfree
  have hfo : IsOfFinOrder γ := by
    rw [← orderOf_pos_iff, hγ]
    exact pow_pos hp.pos _
  have hK : ∀ k ∈ Subgroup.zpowers γ, ∀ u ∈ U, k u ∈ U := by
    intro k hk u hu
    obtain ⟨n, rfl⟩ := hfo.mem_powers_iff_mem_zpowers.2 hk
    exact pow_apply_mem hU n u hu
  set K := Subgroup.zpowers γ with hKdef
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, hγ]
    exact pow_ne_zero _ hp.ne_zero)
  letI act : MulAction K U :=
    { smul := fun k u => ⟨(k : MulAut N) u, hK k k.2 u u.2⟩
      one_smul := fun u => rfl
      mul_smul := fun k k' u => rfl }
  have hsmul : ∀ (k : K) (u : U), ((k • u : U) : N) = (k : MulAut N) u := fun k u => rfl
  have hC : ∀ k : K, ∀ x ∈ ({1} : Set U), k • x ∈ ({1} : Set U) := by
    intro k x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst hx
    exact Subtype.ext (by rw [hsmul]; exact map_one _)
  have hfix : ∀ k : K, k ≠ 1 → ∀ x : U, k • x = x → x ∈ ({1} : Set U) := by
    intro k hk x hkx
    have hk' : (k : MulAut N) ≠ 1 := fun h => hk (Subtype.ext h)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      (Ch3E213M.pow_mem_zpowers_of_ne_one hp hγ k.2 hk')
    have hkx' : (k : MulAut N) ∈ MulAction.stabilizer (MulAut N) (x : N) := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      have := congrArg Subtype.val hkx
      rwa [hsmul] at this
    have h1 := (MulAction.stabilizer (MulAut N) (x : N)).zpow_mem hkx' j
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hj] at h1
    have h2 : (x : N) ∈ U ⊓ fixSub (γ ^ p ^ b) := ⟨x.2, h1⟩
    rw [hfree, Subgroup.mem_bot] at h2
    exact Set.mem_singleton_iff.2 (Subtype.ext h2)
  have h := Ch3E213M.card_dvd_card_sub_of_fixed_subset hC hfix
  rwa [Nat.card_zpowers, hγ, Nat.card_coe_set_eq, Set.ncard_singleton] at h


end Dih

end CFSG.Quasithin.SimsE2
