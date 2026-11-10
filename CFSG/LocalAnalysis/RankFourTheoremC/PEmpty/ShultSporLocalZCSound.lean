module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCCheck
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleSound
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

section Eval

variable {A : Type} [Group A]


end Eval

section Bfs

variable {A : Type} [DecidableEq A]


end Bfs

section Sylow

variable {A : Type} [Group A]

theorem zc_mul_inv_mem_of_finite [Finite A] {E : Set A} {g : A} (h : ∀ x ∈ E, x * g ∈ E) :
    ∀ x ∈ E, x * g⁻¹ ∈ E := by
  have hm : Set.MapsTo (fun x => x * g) E E := fun x hx => h x hx
  have hb := ((Set.toFinite E).injOn_iff_bijOn_of_mapsTo hm).mp
    (fun x _ y _ hxy => mul_right_cancel hxy)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hb.surjOn hx
  simpa using hy


theorem zc_isPGroup_zpowers {G : Type*} [Group G] {t : G} {n : ℕ} (ht : t ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨s, hs⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

theorem zc_exists_conj_mem_of_card {M : Type*} [Group M] [Finite M] (S : Subgroup M) (k : ℕ)
    (hS : Nat.card S = 2 ^ k) (hk : ¬ 2 ^ (k + 1) ∣ Nat.card M) {u : M} (hu : u * u = 1) :
    ∃ g : M, g * u * g⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ k ∣ Nat.card M := by
    rw [← hS]
    exact Subgroup.card_subgroup_dvd_card S
  have hne : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card M).factorization 2 = k := by
    have h1 : k ≤ (Nat.card M).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
    have h2 : ¬ (k + 1 ≤ (Nat.card M).factorization 2) := fun h =>
      hk ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr h)
    omega
  let P : Sylow 2 M := Sylow.ofCard S (by rw [hS, hfac])
  have hP : (P : Subgroup M) = S := rfl
  have hut : u ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hu
  obtain ⟨R, hR⟩ := (zc_isPGroup_zpowers hut).exists_le_sylow
  haveI : Finite (Sylow 2 M) :=
    Finite.of_injective (fun Q : Sylow 2 M => (Q : Set M)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R P
  refine ⟨g, ?_⟩
  rw [← hP, ← hg]
  exact ⟨u, hR (Subgroup.mem_zpowers u), by simp [MulAut.conj_apply]⟩

theorem zc_conj_mem_of_closure {O : List A} {a b : A}
    (h : ∀ x ∈ O, ∀ g ∈ [a, b, a⁻¹, b⁻¹], g * x * g⁻¹ ∈ O) :
    ∀ g ∈ closure ({a, b} : Set A), ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
  have key : ∀ g ∈ closure ({a, b} : Set A),
      (∀ x ∈ O, g * x * g⁻¹ ∈ O) ∧ (∀ x ∈ O, g⁻¹ * x * g ∈ O) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      have hg' : g ∈ [a, b, a⁻¹, b⁻¹] ∧ g⁻¹ ∈ [a, b, a⁻¹, b⁻¹] := by
        rcases hg with hg | hg
        · rw [hg]
          simp
        · rw [Set.mem_singleton_iff.mp hg]
          simp
      exact ⟨fun x hx => h x hx g hg'.1, fun x hx => by simpa using h x hx g⁻¹ hg'.2⟩
    | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul g k _ _ hg hk =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simpa [mul_assoc] using hg.1 _ (hk.1 x hx)
      · simpa [mul_assoc] using hk.2 _ (hg.2 x hx)
    | inv g _ hg =>
      exact ⟨fun x hx => by simpa using hg.2 x hx, fun x hx => by simpa using hg.1 x hx⟩
  exact fun g hg => (key g hg).1

end Sylow

section Closure

variable {A : Type} [Group A]

theorem zc_mem_normalizer_of_conj_mem [Finite A] (K : Subgroup A) {h : A}
    (hK : ∀ v ∈ K, h * v * h⁻¹ ∈ K) : h ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hK x, fun hx => ?_⟩
  have hm : Set.MapsTo (fun v => h * v * h⁻¹) (K : Set A) (K : Set A) := fun v hv => hK v hv
  have hb := ((Set.toFinite (K : Set A)).injOn_iff_bijOn_of_mapsTo hm).mp (by
    intro v _ w _ hvw
    simpa using hvw)
  obtain ⟨y, hy, hyx⟩ := hb.surjOn hx
  have : y = x := by simpa using hyx
  rw [← this]
  exact hy


theorem zc_exists_pow_lt_of_mem_zpowers {G : Type*} [Group G] [Finite G] {z g : G} {p : ℕ}
    (hz : orderOf z = p) (hg : g ∈ zpowers z) : ∃ i < p, g = z ^ i := by
  classical
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have h := hfin.mem_zpowers_iff_mem_range_orderOf.mp hg
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hz ▸ hi, rfl⟩


theorem zc_mem_zConjClosure_iff [Finite A] {M : Subgroup A} {z₀ u : A} (hz : z₀ ∈ M) (hu : u ∈ M)
    {p : ℕ} (hord : orderOf (⟨z₀, hz⟩ : M) = p) (cs : List A)
    (hcs : ∀ x, x ∈ cs ↔ ∃ i < p, x = z₀ ^ i * u * (z₀ ^ i)⁻¹) (v : M) :
    v ∈ zConjClosure (⟨z₀, hz⟩ : M) ⟨u, hu⟩ ↔ (v : A) ∈ closure {c | c ∈ cs} := by
  have hmap : (zConjClosure (⟨z₀, hz⟩ : M) ⟨u, hu⟩).map M.subtype = closure {c | c ∈ cs} := by
    rw [zConjClosure, MonoidHom.map_closure]
    congr 1
    ext c
    simp only [Set.mem_image, Set.mem_setOf_eq, hcs]
    constructor
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨i, hi, rfl⟩ := zc_exists_pow_lt_of_mem_zpowers hord hg
      exact ⟨i, hi, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨(⟨z₀, hz⟩ : M) ^ i, pow_mem (mem_zpowers _) i, rfl⟩, by simp⟩
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm

end Closure

section PerU


end PerU

section Main


end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
