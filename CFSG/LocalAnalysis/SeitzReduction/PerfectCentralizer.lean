module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.EvenSmallLie.Setup
import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute)
open CFSG.ComponentClassification.SolvableKernelContainment (perfect_solvable_subsingleton)
open CFSG.ComponentClassification.StandardRecognition
  (standard_cyclic_local_centralizer_kernel_two_group)

section General

variable {G : Type*} [Group G]

theorem perfect_eq_bot_of_le {A P : Subgroup G} (hA : Group.IsSolvable A) (hP : ⁅P, P⁆ = P)
    (hPA : P ≤ A) : P = ⊥ := by
  have : Group.IsPerfect P := isPerfect_iff.mpr hP
  have : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective (inclusion_injective hPA)
  have : Subsingleton P := perfect_solvable_subsingleton
  exact eq_bot_of_subsingleton P

theorem perfect_le_ker {Q : Type*} [Group Q] [Group.IsSolvable Q] (f : G →* Q)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) : P ≤ f.ker := by
  rw [← Subgroup.map_eq_bot_iff]
  exact perfect_eq_bot_of_le (A := ⊤) inferInstance (by rw [← map_commutator, hP]) le_top

theorem commutator_subgroupOf_eq_self {H P : Subgroup G} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) :
    ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
  have : Group.IsPerfect P := isPerfect_iff.mpr hP
  have : Group.IsPerfect (P.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hPH).symm.surjective
  exact commutator_eq_self

theorem perfect_le_of_le_sup {L K P : Subgroup G} (hKL : K ≤ normalizer (L : Set G))
    (hK : Group.IsSolvable K) (hP : ⁅P, P⁆ = P) (hPLK : P ≤ L ⊔ K) : P ≤ L := by
  set N := normalizer (L : Set G) with hN
  have hLN : L ≤ N := le_normalizer
  have hPN : P ≤ N := hPLK.trans (sup_le hLN hKL)
  set π := QuotientGroup.mk' (L.subgroupOf N) with hπ
  have hKs : Group.IsSolvable ((K.subgroupOf N).map π) := by
    have : Group.IsSolvable (K.subgroupOf N) :=
      Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hKL).toMonoidHom)
        (subgroupOfEquivOfLe hKL).injective
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (K.subgroupOf N))
  have hPK : (P.subgroupOf N).map π ≤ (K.subgroupOf N).map π := by
    calc (P.subgroupOf N).map π ≤ ((L ⊔ K).subgroupOf N).map π :=
          map_mono fun x hx => mem_subgroupOf.2 (hPLK (mem_subgroupOf.1 hx))
      _ = (K.subgroupOf N).map π := by
          rw [subgroupOf_sup hLN hKL, Subgroup.map_sup,
            (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' (L.subgroupOf N)).ge, bot_sup_eq]
  have hbot := perfect_eq_bot_of_le hKs
    (by rw [← map_commutator, commutator_subgroupOf_eq_self hPN hP]) hPK
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro x hx
  exact mem_subgroupOf.1 (hbot (mem_subgroupOf.2 (show ((⟨x, hPN hx⟩ : N) : G) ∈ P from hx)))

theorem perfect_le_sup_centralizer {L P : Subgroup G} (hOut : Group.IsSolvable (Outer L))
    (hP : ⁅P, P⁆ = P) (hPN : P ≤ normalizer (L : Set G)) :
    P ≤ L ⊔ centralizer (L : Set G) := by
  have : Group.IsPerfect P := isPerfect_iff.mpr hP
  intro p hp
  obtain ⟨l, hl⟩ := perfect_action_inner (L.normalizerMonoidHom.comp (inclusion hPN)) ⟨p, hp⟩
  have hc : (l : G)⁻¹ * p ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 : p * x * p⁻¹ = l * x * (l : G)⁻¹ := by
      have := congrArg (fun a : MulAut L => ((a ⟨x, hx⟩ : L) : G)) hl
      simpa [MulAut.conj_apply] using this
    calc x * ((l : G)⁻¹ * p) = (l : G)⁻¹ * (l * x * (l : G)⁻¹) * p := by group
      _ = (l : G)⁻¹ * (p * x * p⁻¹) * p := by rw [h1]
      _ = (l : G)⁻¹ * p * x := by group
  have hp' : p = l * ((l : G)⁻¹ * p) := by group
  rw [hp']
  exact mul_mem_sup l.2 hc

theorem perfect_le_of_le_sup_centralizer {L H P : Subgroup G} (hLH : L ≤ H)
    (hK : Group.IsSolvable (centralizer (L : Set G) ⊓ H : Subgroup G)) (hP : ⁅P, P⁆ = P)
    (hPH : P ≤ H) (hPLC : P ≤ L ⊔ centralizer (L : Set G)) : P ≤ L := by
  refine perfect_le_of_le_sup (K := centralizer (L : Set G) ⊓ H)
    (inf_le_left.trans (centralizer_le_normalizer _)) hK hP fun p hp => ?_
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun l hl c hc => mem_centralizer_iff.1 hc l hl) (hPLC hp)
  have hcH : c ∈ H := by
    have := H.mul_mem (H.inv_mem (hLH hl)) (hPH hp)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  exact mul_mem_sup hl ⟨hc, hcH⟩

theorem perfect_le_of_isSolvable_outer {L H P : Subgroup G} (hOut : Group.IsSolvable (Outer L))
    (hLH : L ≤ H) (hHN : H ≤ normalizer (L : Set G))
    (hK : Group.IsSolvable (centralizer (L : Set G) ⊓ H : Subgroup G)) (hP : ⁅P, P⁆ = P)
    (hPH : P ≤ H) : P ≤ L :=
  perfect_le_of_le_sup_centralizer hLH hK hP hPH
    (perfect_le_sup_centralizer hOut hP (hPH.trans hHN))

theorem le_centralizer_of_mem_centralizer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) : L ≤ centralizer ({t} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)


end General

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inf_centralizer_isCyclic_of_standard (hL : standardComponentIsStandard L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨S', hS'⟩ := hcyc
  obtain ⟨⟨-, h1, h2⟩, -⟩ := standard_cyclic_local_centralizer_kernel_two_group hL S
    ((Sylow.equiv S S').isCyclic.mpr hS') (hS (mem_zpowers tC)) htC2 hcore
  exact ⟨h1, h2⟩

theorem perfect_le_of_le_sup_centralizer_of_standard (hL : standardComponentIsStandard L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPt : P ≤ centralizer ({t} : Set G))
    (hPLC : P ≤ L ⊔ centralizer (L : Set G)) : P ≤ L := by
  have : IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    (inf_centralizer_isCyclic_of_standard hL hcyc htC ht hcore).1
  exact perfect_le_of_le_sup_centralizer (le_centralizer_of_mem_centralizer htC) inferInstance
    hP hPt hPLC

theorem perfect_le_of_standard (hL : standardComponentIsStandard L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPt : P ≤ centralizer ({t} : Set G)) : P ≤ L :=
  perfect_le_of_le_sup_centralizer_of_standard hL hcyc htC ht hcore hP hPt
    (perfect_le_sup_centralizer hOut hP
      (hPt.trans (centralizer_le_normalizer_of_standard hL htC ht)))

theorem std_perfect_le (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPt : P ≤ centralizer ({t} : Set G)) : P ≤ L :=
  perfect_le_of_standard hset.standard hset.cyclic hOut htC ht (hset.core t ht) hP hPt


theorem std_perfect_le_inf_conjugate (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (g : G) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPt : P ≤ centralizer ({t} : Set G)) (hPtg : P ≤ centralizer ({g⁻¹ * t * g} : Set G)) :
    P ≤ L ⊓ conjugate L g := by
  refine le_inf (std_perfect_le hset hOut htC ht hP hPt) ?_
  set P' := P.map (MulAut.conj g).toMonoidHom with hP'def
  have hP' : ⁅P', P'⁆ = P' := by rw [hP'def, ← map_commutator, hP]
  have hP't : P' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (hPtg hp)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * p * g⁻¹ * t = g * (p * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * p) * g⁻¹ := by rw [h]
      _ = t * (g * p * g⁻¹) := by group
  have hP'L := std_perfect_le hset hOut htC ht hP' hP't
  intro p hp
  show p ∈ L.map (MulAut.conj g⁻¹).toMonoidHom
  refine ⟨g * p * g⁻¹, hP'L ⟨p, hp, by simp [MulAut.conj_apply]⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group


end Standard

end CFSG.SeitzReduction
