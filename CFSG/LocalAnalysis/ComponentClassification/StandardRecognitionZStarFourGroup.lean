module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup
open CFSG.ClassicalInvolution (orderOf_conj_eq)

variable {G : Type*} [Group G]

section FourGroup

variable {t p : G}

theorem mem_closure_pair_iff (htt : t * t = 1) (hpp : p * p = 1) (htp : t * p = p * t)
    {x : G} : x ∈ Subgroup.closure ({t, p} : Set G) ↔ x = 1 ∨ x = t ∨ x = p ∨ x = t * p := by
  have htt' : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, htt, one_mul]
  have hpt : p * t = t * p := htp.symm
  have hpt' : ∀ y, p * (t * y) = t * (p * y) := fun y => by rw [← mul_assoc, hpt, mul_assoc]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, one_mul, mul_one, htt, hpp, htt', hpt, hpt', true_or, or_true]
    | inv x _ hx =>
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, htinv, hpinv, mul_inv_rev, hpt, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem commute_and_mul_self_of_mem_closure_pair (htt : t * t = 1) (hpp : p * p = 1)
    (htp : t * p = p * t) {x y : G} (hx : x ∈ Subgroup.closure ({t, p} : Set G))
    (hy : y ∈ Subgroup.closure ({t, p} : Set G)) : x * y = y * x ∧ x * x = 1 := by
  have htt' : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, htt, one_mul]
  have hpt : p * t = t * p := htp.symm
  have hpt' : ∀ y, p * (t * y) = t * (p * y) := fun y => by rw [← mul_assoc, hpt, mul_assoc]
  rw [mem_closure_pair_iff htt hpp htp] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, one_mul, mul_one, htt, hpp, htt', hpt, hpt', and_self]

theorem card_closure_pair_of_involutions (htt : t * t = 1) (hpp : p * p = 1) (htp : t * p = p * t)
    (ht1 : t ≠ 1) (hp1 : p ≠ 1) (hne : t ≠ p) :
    Nat.card (Subgroup.closure ({t, p} : Set G)) = 4 := by
  have hset : ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) = {1, t, p, t * p} := by
    ext x
    simp only [SetLike.mem_coe, mem_closure_pair_iff htt hpp htp, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have htp1 : t * p ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right htt])
  change Nat.card ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simpa using ht1
  · simpa [not_or] using ⟨hne, hp1⟩
  · simpa [not_or, eq_comm] using ⟨ht1, hp1, htp1⟩

theorem isElementaryAbelian_closure_pair (htt : t * t = 1) (hpp : p * p = 1)
    (htp : t * p = p * t) : CFSG.IsElementaryAbelian 2 (Subgroup.closure ({t, p} : Set G)) where
  is_comm := ⟨fun x y => Subtype.ext
    (commute_and_mul_self_of_mem_closure_pair htt hpp htp x.2 y.2).1⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    simpa [sq] using (commute_and_mul_self_of_mem_closure_pair htt hpp htp x.2 x.2).2)

theorem conj_mem_closure_pair_of_conj_mem {g : G}
    (hgt : g * t * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G))
    (hgp : g * p * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G)) {x : G}
    (hx : x ∈ Subgroup.closure ({t, p} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G) := by
  have hle : Subgroup.closure ({t, p} : Set G) ≤
      (Subgroup.closure ({t, p} : Set G)).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro y (rfl | rfl)
    · simpa [MulAut.conj_apply] using hgt
    · simpa [MulAut.conj_apply] using hgp
  simpa [MulAut.conj_apply] using hle hx


end FourGroup

theorem exists_swap_of_external_fusion {t p : G} {K : Subgroup G} (ht : orderOf t = 2)
    (htK : t ∈ K) (hfus : ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hpH : p ∈ centralizer ({t} : Set G)) (hpK : p ∉ K) (hpt : ∃ g : G, g⁻¹ * t * g = p) :
    ∃ b : G, b * t * b⁻¹ = p ∧ b * p * b⁻¹ = t := by
  obtain ⟨g, hg⟩ := hpt
  have hpt' : p * t = t * p := mem_centralizer_singleton_iff.mp hpH
  rw [← hg] at hpt'
  have hyH : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g * t) * g⁻¹ := by rw [hpt']
      _ = t * (g * t * g⁻¹) := by group
  have hyK : g * t * g⁻¹ ∉ K := by
    intro hyK
    have h := hfus g⁻¹ (by simpa using hyK)
    rw [inv_inv] at h
    apply hpK
    rw [← hg]
    have : g⁻¹ * t * g = t := by
      calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
        _ = t := by group
    rw [this]
    exact htK
  have hp2 : orderOf p = 2 := by
    rw [← hg, show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
  have hy2 : orderOf (g * t * g⁻¹) = 2 := by rw [orderOf_conj_eq, ht]
  obtain ⟨h, hhH, hh⟩ := hext p _ hpH hpK hp2 hyH hyK hy2
  have hht : h * t = t * h := mem_centralizer_singleton_iff.mp hhH
  refine ⟨g⁻¹ * h⁻¹, ?_, ?_⟩
  · calc g⁻¹ * h⁻¹ * t * (g⁻¹ * h⁻¹)⁻¹ = g⁻¹ * (h⁻¹ * (t * h)) * g := by group
      _ = g⁻¹ * (h⁻¹ * (h * t)) * g := by rw [hht]
      _ = g⁻¹ * t * g := by group
      _ = p := hg
  · calc g⁻¹ * h⁻¹ * p * (g⁻¹ * h⁻¹)⁻¹ = g⁻¹ * (h⁻¹ * p * h) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hh]
      _ = t := by group


end CFSG.ComponentClassification.StandardRecognition
