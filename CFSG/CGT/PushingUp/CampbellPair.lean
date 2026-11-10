module

import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne
open scoped commutatorElement

section Characteristic

variable {G : Type} [Group G]

private theorem exists_mulAut_restrict {P S : Subgroup G} (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) (φ : MulAut P) :
    ∃ ψ : MulAut S, ∀ s : S, ((ψ s : S) : G) = ((φ ⟨s, hSP s.2⟩ : P) : G) := by
  have hmem : ∀ (χ : MulAut P) (s : S), ((χ ⟨s, hSP s.2⟩ : P) : G) ∈ S := fun χ s =>
    (Subgroup.characteristic_iff_le_comap.mp hS) χ s.2
  exact ⟨{ toFun := fun s => ⟨(φ ⟨s, hSP s.2⟩ : P), hmem φ s⟩
           invFun := fun s => ⟨(φ.symm ⟨s, hSP s.2⟩ : P), hmem φ.symm s⟩
           left_inv := fun s => Subtype.ext (by simp)
           right_inv := fun s => Subtype.ext (by simp)
           map_mul' := fun a b => Subtype.ext (by
             have h := congrArg (fun y : P => (y : G)) (map_mul φ ⟨a, hSP a.2⟩ ⟨b, hSP b.2⟩)
             exact h) }, fun s => rfl⟩

theorem characteristic_trans {T₁ S P : Subgroup G} (h₁ : T₁ ≤ S) (h₂ : S ≤ P)
    (hT : (T₁.subgroupOf S).Characteristic) (hS : (S.subgroupOf P).Characteristic) :
    (T₁.subgroupOf P).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨ψ, hψ⟩ := exists_mulAut_restrict h₂ hS φ
  have hxS : (x : G) ∈ S := h₁ hx
  have h := (Subgroup.characteristic_iff_le_comap.mp hT) ψ (show (⟨x, hxS⟩ : S) ∈ _ from hx)
  change ((ψ ⟨x, hxS⟩ : S) : G) ∈ T₁ at h
  rw [hψ] at h
  exact h

theorem normalizer_le_normalizer_of_characteristic' {C P : Subgroup G} (hCP : C ≤ P)
    (hC : (C.subgroupOf P).Characteristic) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (P : Set G) → ∀ {w : G}, w ∈ C →
      g * w * g⁻¹ ∈ C := by
    intro g hg w hw
    let φ : MulAut P := Subgroup.normalizerMonoidHom P ⟨g, hg⟩
    exact (Subgroup.characteristic_iff_le_comap.mp hC) φ (show (⟨w, hCP hw⟩ : P) ∈ _ from hw)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key hg hh, fun hh => ?_⟩
  have := key (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

private theorem comm_map_of_forall_comm {P : Subgroup G} (φ : MulAut P) {x : P}
    (hx : ∀ k ∈ P, k * (x : G) = x * k) : ∀ k ∈ P, k * ((φ x : P) : G) = (φ x) * k := by
  intro k hk
  have h1 : φ.symm ⟨k, hk⟩ * x = x * φ.symm ⟨k, hk⟩ := Subtype.ext (hx _ (φ.symm ⟨k, hk⟩).2)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2


end Characteristic

section PushingUpS

variable {G : Type} [Group G]

theorem pushingUpS_le (P : Subgroup G) : pushingUpS P ≤ P :=
  inf_le_left

private theorem mem_pushingUpS_iff {P : Subgroup G} {x : G} :
    x ∈ pushingUpS P ↔ x ∈ P ∧
      ∀ z ∈ inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P, z * x = x * z := by
  simp [pushingUpS, Subgroup.mem_centralizer_iff]

theorem characteristic_pushingUpS [Finite G] (P : Subgroup G) :
    ((pushingUpS P).subgroupOf P).Characteristic := by
  have h : (pushingUpS P).subgroupOf P =
      Subgroup.centralizer (elemThompsonCenterTorsion ↥P 2 : Set ↥P) := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_pushingUpS_iff, Subgroup.mem_centralizer_iff]
    refine ⟨fun h e he => ?_, fun hx => ⟨x.2, ?_⟩⟩
    · exact Subtype.ext (h.2 _ ⟨e, he, rfl⟩)
    · rintro _ ⟨e, he, rfl⟩
      exact congrArg Subtype.val (hx e he)
  rw [h]
  have := BlueprintB2.elemThompsonCenterTorsion_characteristic P 2
  infer_instance


theorem mem_omegaOneCenterIn_iff {P : Subgroup G} {z : G} :
    z ∈ omegaOneCenterIn P ↔ z ∈ P ∧ (∀ k ∈ P, k * z = z * k) ∧ z ^ 2 = 1 := by
  have h : omegaOneCenterIn P = BlueprintB2.centerTorsion 2 P :=
    (BlueprintB2.centerTorsion_eq_closure 2 P).symm
  rw [h]
  exact BlueprintB2.mem_centerTorsion_iff

theorem omegaOneCenterIn_le (P : Subgroup G) : omegaOneCenterIn P ≤ P :=
  fun _ h => (mem_omegaOneCenterIn_iff.mp h).1

theorem characteristic_omegaOneCenterIn (P : Subgroup G) :
    ((omegaOneCenterIn P).subgroupOf P).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨-, hc, hsq⟩ := mem_omegaOneCenterIn_iff.mp (Subgroup.mem_subgroupOf.mp hx)
  refine Subgroup.mem_subgroupOf.mpr (mem_omegaOneCenterIn_iff.mpr
    ⟨(φ x).2, comm_map_of_forall_comm φ hc, ?_⟩)
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have h2 : (φ x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  simpa using congrArg Subtype.val h2


private theorem exists_mem_center_orderOf_two {K : Type*} [Group K] [Finite K] [Nontrivial K]
    (hK : IsPGroup 2 K) : ∃ z ∈ Subgroup.center K, orderOf z = 2 := by
  have hc : Nontrivial (Subgroup.center K) := hK.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center K) := hK.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center K) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨(x : K), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem omegaOneCenterIn_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    omegaOneCenterIn P ≠ ⊥ := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨x, hxc, hx2⟩ := exists_mem_center_orderOf_two hP
  have hxsq : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hgmem : (x : G) ∈ omegaOneCenterIn P :=
    mem_omegaOneCenterIn_iff.mpr ⟨x.2, fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩), by
        simpa using congrArg Subtype.val hxsq⟩
  intro h
  rw [h, Subgroup.mem_bot] at hgmem
  have hx1 : x = 1 := Subtype.ext hgmem
  rw [hx1, orderOf_one] at hx2
  omega


end PushingUpS

section General

variable {G : Type} [Group G]


end General

section Automorphisms


end Automorphisms

section Triples

private theorem tripleE_normal (H : Type) [Group H] [Finite H] : (tripleE H).Normal :=
  elemCenterIn_normal 2 (pCore 2 H)

private theorem tripleE_le_pCore (H : Type) [Group H] : tripleE H ≤ pCore 2 H :=
  Subgroup.map_subtype_le _


private theorem tripleV_le_tripleE (H : Type) [Group H] [Finite H] : tripleV H ≤ tripleE H := by
  have := tripleE_normal H
  exact Subgroup.commutator_le_right _ _


end Triples

section InClassGFacts


variable {S H : Type} [Group S] [Group H] [Finite H] {ι : S →* H}

private theorem pCore_le_range (hG : InClassG S H ι) : pCore 2 H ≤ ι.range := by
  have hp : IsPGroup 2 ι.range := hG.sylow.2.1
  have hidx : ¬ 2 ∣ ι.range.index := by
    have := hG.sylow.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (hp.toSylow hidx)

private theorem tripleE_le_range (hG : InClassG S H ι) : tripleE H ≤ ι.range :=
  (tripleE_le_pCore H).trans (pCore_le_range hG)


end InClassGFacts

section Pair


end Pair

end CFSG.CGT.PushingUp
