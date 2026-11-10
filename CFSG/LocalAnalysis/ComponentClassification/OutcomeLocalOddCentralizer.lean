module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup

section Images

variable {F A : Type*} [Group F] [Group A]

theorem map_conjugate (η : F →* A) (H : Subgroup F) (g : F) :
    (CFSG.conjugate H g).map η = CFSG.conjugate (H.map η) (η g) := by
  unfold CFSG.conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp


variable {η : F →* A}


theorem map_inf_of_ker_le {X Y : Subgroup F} (hη : Function.Surjective η) (hX : η.ker ≤ X)
    (hY : η.ker ≤ Y) : (X ⊓ Y).map η = X.map η ⊓ Y.map η := by
  rw [← map_comap_eq_self_of_surjective hη (X.map η ⊓ Y.map η), comap_inf, comap_map_eq,
    comap_map_eq, sup_eq_left.mpr hX, sup_eq_left.mpr hY]


end Images

section Semisimple

variable {F : Type*} [Group F] {ι : Type*} {S : ι → Subgroup F}

theorem iSup_le_normalizer
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y) (i : ι) :
    (⨆ j, S j) ≤ normalizer (S i : Set F) := by
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact le_normalizer
  · exact le_trans (fun y hy => mem_centralizer_iff.mpr fun h hh => (hcomm hji y h hy hh).eq.symm)
      (centralizer_le_normalizer _)


end Semisimple

section Involutions

variable {F : Type*} [Group F]

theorem exists_mul_mem_centralizer_of_odd {K : Subgroup F} [K.Normal] (hK : Odd (Nat.card K))
    {a f : F} (ha : a ^ 2 = 1) (hf : f * a * f⁻¹ * a⁻¹ ∈ K) :
    ∃ k ∈ K, k * f ∈ centralizer ({a} : Set F) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  set a' := f * a * f⁻¹ with ha'
  set k₁ := a⁻¹ * a' with hk₁
  have hk₁K : k₁ ∈ K := by
    have := (inferInstance : K.Normal).conj_mem _ hf a⁻¹
    rwa [show a⁻¹ * (f * a * f⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * a' by rw [ha']; group] at this
  have ha'sq : a' * a' = 1 := by
    rw [ha', show f * a * f⁻¹ * (f * a * f⁻¹) = f * (a * a) * f⁻¹ by group, ← sq, ha, mul_one,
      mul_inv_cancel]
  have hinv : a * k₁ * a⁻¹ = k₁⁻¹ := by
    have h : a * k₁ * (a * k₁) = 1 := by
      rw [hk₁, mul_inv_cancel_left]
      exact ha'sq
    have h' : a * k₁ * a * k₁ = 1 := by rw [← h]; group
    rw [hainv]
    exact mul_eq_one_iff_eq_inv.mp h'
  have hodd : Odd (orderOf k₁) := Odd.of_dvd_nat hK (Subgroup.orderOf_dvd_natCard K hk₁K)
  obtain ⟨t, ht⟩ := hodd
  set c := k₁ ^ (t + 1) with hc
  have hcK : c ∈ K := pow_mem hk₁K _
  have hcc : c * c = k₁ := by
    rw [hc, ← pow_add, show t + 1 + (t + 1) = orderOf k₁ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, ← conj_pow, hinv, inv_pow]
  refine ⟨c, hcK, ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hkey : c * a' * c⁻¹ = a := by
    have : a' = a * (c * c) := by rw [hcc, hk₁]; group
    rw [this]
    calc c * (a * (c * c)) * c⁻¹ = c * (a * c * a⁻¹) * a := by group
      _ = a := by rw [hac]; group
  calc c * f * a = c * a' * c⁻¹ * (c * f) := by rw [ha']; group
    _ = a * (c * f) := by rw [hkey]

end Involutions

section Standard


end Standard

section Main


end Main

end CFSG.ComponentClassification.OutcomeLocal
