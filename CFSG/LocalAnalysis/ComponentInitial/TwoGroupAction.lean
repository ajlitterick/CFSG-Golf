module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {F : Type*} [Group F]

namespace TwoGroupAction

theorem exists_sylow_le_normalizer [Finite F] {p : ℕ} [Fact p.Prime] {N Q : Subgroup F}
    (hQ : IsPGroup p Q) (hQN : Q ≤ normalizer (N : Set F)) :
    ∃ P : Sylow p N, Q ≤ normalizer (((P : Subgroup N).map N.subtype : Subgroup F) : Set F) := by
  classical
  let Q' : Subgroup (normalizer (N : Set F)) := Q.subgroupOf (normalizer (N : Set F))
  have hQ' : IsPGroup p Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  obtain ⟨P, hP⟩ :=
    hQ'.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p N) (not_dvd_card_sylow p N)
  refine ⟨P, fun q hq => ?_⟩
  have key : ∀ g : Q', ∀ y ∈ (P : Subgroup N).map N.subtype,
      ((g : normalizer (N : Set F)) : F) * y * ((g : normalizer (N : Set F)) : F)⁻¹ ∈
        (P : Subgroup N).map N.subtype := by
    rintro g _ ⟨n, hn, rfl⟩
    have hgP : g • P = P := hP g
    have hmem : (g : normalizer (N : Set F)) • n ∈ ((g • P : Sylow p N) : Subgroup N) := by
      rw [show (g • P : Sylow p N) = (g : normalizer (N : Set F)) • P from rfl,
        Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul n _ _ hn
    rw [hgP] at hmem
    exact ⟨_, hmem, Subgroup.smul_coe N _ n⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key ⟨⟨q, hQN hq⟩, hq⟩ y, fun hy => ?_⟩
  simpa [mul_assoc] using key ⟨⟨q, hQN hq⟩, hq⟩⁻¹ _ hy

theorem sylow_map_eq_of_le {p : ℕ} {N X : Subgroup F} (P : Sylow p N) (hX : IsPGroup p X)
    (hXN : X ≤ N) (hPX : (P : Subgroup N).map N.subtype ≤ X) :
    X = (P : Subgroup N).map N.subtype := by
  have hX' : IsPGroup p (X.subgroupOf N) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm
  have hle : (P : Subgroup N) ≤ X.subgroupOf N := fun n hn => hPX ⟨n, hn, rfl⟩
  rw [← P.is_maximal' hX' hle, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXN]


theorem exists_mem_normalizer_of_lt [Finite F] {p : ℕ} [Fact p.Prime] {X Y : Subgroup F}
    (hY : IsPGroup p Y) (hXY : X < Y) : ∃ w ∈ Y, w ∉ X ∧ w ∈ normalizer (X : Set F) := by
  have hlt : X.subgroupOf Y < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hXY.not_ge ?_
    rwa [Subgroup.subgroupOf_eq_top] at h
  obtain ⟨V, hle, hnormal, hidx⟩ := p_group_normalizer_step hY hlt
  have hnot : ¬ V ≤ X.subgroupOf Y := fun h => by
    have h1 := Subgroup.relIndex_eq_one.2 h
    rw [hidx] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  obtain ⟨w, hwV, hwX⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  refine ⟨w, w.2, hwX, ?_⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : (⟨⟨h, hXY.le hh⟩, hle hh⟩ : V) ∈ (X.subgroupOf Y).subgroupOf V := hh
    exact hnormal.conj_mem _ hmem ⟨w, hwV⟩
  · intro hh
    have hY' : (w : F) * h * (w : F)⁻¹ ∈ Y := hXY.le hh
    have hhY : h ∈ Y := by
      simpa [mul_assoc] using Y.mul_mem (Y.mul_mem (Y.inv_mem w.2) hY') w.2
    have hwh : (⟨h, hhY⟩ : Y) = w⁻¹ * ⟨(w : F) * h * (w : F)⁻¹, hY'⟩ * w :=
      Subtype.ext (by simp [mul_assoc])
    have hmem : (⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ : V) ∈
        (X.subgroupOf Y).subgroupOf V := hh
    have hconj := hnormal.conj_mem _ hmem ⟨w, hwV⟩⁻¹
    have h2 : ((⟨w, hwV⟩⁻¹ * ⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ * (⟨w, hwV⟩⁻¹)⁻¹ : V) :
        Y) = ⟨h, hhY⟩ := by
      rw [hwh]
      simp
    change (((⟨w, hwV⟩⁻¹ * ⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ * (⟨w, hwV⟩⁻¹)⁻¹ : V) :
      Y) : F) ∈ X at hconj
    rwa [h2] at hconj


end TwoGroupAction

open TwoGroupAction


end CFSG.LocalAnalysis.ComponentInitial
