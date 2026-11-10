module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem isCompl_fixed_commOf_of_odd [Finite A] (hodd : Odd (Nat.card A))
    (hQ : ∀ q : Q, q ^ 2 = 1) :
    IsCompl (fixed A (⊤ : Subgroup Q)) (commOf A (⊤ : Subgroup Q)) := by
  classical
  have := Fintype.ofFinite A
  have hn : Odd (Fintype.card A) := by rwa [← Nat.card_eq_fintype_card]
  have hpow : ∀ q : Q, q ^ Fintype.card A = q := by
    intro q
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_succ, pow_mul, hQ q, one_pow, one_mul]
  let N : Q →* Q :=
    { toFun := fun q => ∏ a : A, a • q
      map_one' := by simp
      map_mul' := fun x y => by simp only [smul_mul']; exact Finset.prod_mul_distrib }
  have hNdef : ∀ q, N q = ∏ a : A, a • q := fun q => rfl
  have hN_smul : ∀ (b : A) (q : Q), N (b • q) = N q := by
    intro b q
    rw [hNdef, hNdef]
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ (fun a => rfl)
  have hN_fixed : ∀ q : Q, N q ∈ fixed A (⊤ : Subgroup Q) := by
    intro q
    refine ⟨trivial, fun b => ?_⟩
    have h1 := map_prod (MulDistribMulAction.toMonoidHom Q b) (fun a : A => a • q) Finset.univ
    have h2 : b • ∏ a : A, a • q = ∏ a : A, b • a • q := h1
    rw [hNdef, h2]
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun a => rfl)
  have hN_ker : ∀ q ∈ commOf A (⊤ : Subgroup Q), N q = 1 := by
    intro q hq
    have : commOf A (⊤ : Subgroup Q) ≤ N.ker := by
      rw [commOf_le_iff]
      intro a l _
      rw [MonoidHom.mem_ker, map_mul, map_inv, hN_smul, mul_inv_cancel]
    exact this hq
  have hN_self : ∀ q ∈ fixed A (⊤ : Subgroup Q), N q = q := by
    intro q hq
    rw [hNdef]
    simp_rw [hq.2]
    rw [Finset.prod_const, Finset.card_univ, hpow]
  have hdecomp : ∀ q : Q, q * (N q)⁻¹ ∈ commOf A (⊤ : Subgroup Q) := by
    intro q
    have h1 : q * (N q)⁻¹ = ∏ a : A, (q * (a • q)⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hpow, hNdef,
        Finset.prod_inv_distrib]
    rw [h1]
    refine Subgroup.prod_mem _ fun a _ => ?_
    have : q * (a • q)⁻¹ = ((a • q) * q⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem (mem_commOf_of_mem a trivial)
  rw [isCompl_iff, disjoint_iff_inf_le, codisjoint_iff]
  constructor
  · intro q ⟨hq1, hq2⟩
    rw [Subgroup.mem_bot, ← hN_self q hq1]
    exact hN_ker q hq2
  · rw [eq_top_iff]
    intro q _
    have : q = N q * (q * (N q)⁻¹) := by
      rw [mul_comm q, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup (hN_fixed q) (hdecomp q)

end XMod

section Dihedral

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

theorem eq_one_or_eq_of_mem_zpowers_of_sq {t a : G} (ht : t ^ 2 = 1)
    (ha : a ∈ Subgroup.zpowers t) : a = 1 ∨ a = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have ht' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact ht
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, ht', one_zpow]
  · right; rw [zpow_add_one, zpow_mul, ht', one_zpow, one_mul]


theorem mem_normalizer_zpowers_of_inv {t x : G} (ht : t ^ 2 = 1) (hx : t * x * t⁻¹ = x⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have h2 : t * t = 1 := by rw [← sq]; exact ht
  have h3 : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  have key : ∀ h ∈ Subgroup.zpowers x, t * h * t⁻¹ ∈ Subgroup.zpowers x := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, hx]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers x)) k
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key h, fun hh => ?_⟩
  have := key _ hh
  rwa [h3, ← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, h2, mul_one] at this

theorem smul_top_eq_top (g : G) : g • (⊤ : Subgroup V) = ⊤ := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp


end Dihedral

end CFSG.Quasithin
