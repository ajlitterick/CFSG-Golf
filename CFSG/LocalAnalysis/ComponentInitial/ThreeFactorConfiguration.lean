module

public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor
public import CFSG.LocalAnalysis.ComponentInitial.ComponentTypeLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentInitial.BlockTransporter

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Bridges

variable {X : Type*} [Group X]

theorem assembly_isSubnormal_iff_subgroupOf {K H : Subgroup X} (hKH : K ≤ H) :
    CFSG.Assembly.IsSubnormal K H ↔ (K.subgroupOf H).IsSubnormal :=
  CFSG.Assembly.IsSubnormal.iff_subgroupOf hKH

theorem isTwoPComponent_iff_isPComponent (L : Subgroup X) :
    CFSG.Assembly.ComponentType.IsTwoPComponent L ↔ CFSG.IsPComponent 2 L := by
  have key : ∀ (N : Subgroup X) [N.Normal], N = pPrimeCore 2 X →
      ((∃ K : Subgroup (X ⧸ N), CFSG.Assembly.IsComponentOf K ⊤ ∧
        CFSG.Assembly.IsSubnormal L ⊤ ∧ L.map (QuotientGroup.mk' N) = K ∧
        ∀ J : Subgroup X, J < L → CFSG.Assembly.IsSubnormal J ⊤ →
          J.map (QuotientGroup.mk' N) ≠ K) ↔ CFSG.IsPComponent 2 L) := by
    rintro N _ rfl
    unfold CFSG.IsPComponent
    simp only [AssemblyBPredicates.isComponentOf_top_iff_native,
      AssemblyBPredicates.isSubnormal_top_iff_mathlib]
  exact key _ assembly_oddCore_eq_pPrimeCore


theorem two_components_ordinary_of_localB {G : Type*} [Group G] [Finite G]
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {S0 F : Subgroup G} (hS0 : S0 ≠ ⊥)
    (hS02 : IsPGroup 2 S0) (hFN : F ≤ normalizer (S0 : Set G))
    (hsub : CFSG.Assembly.IsSubnormal F (normalizer (S0 : Set G))) :
    ∀ L : Subgroup F, CFSG.IsPComponent 2 L → CFSG.IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF'sub : (F.subgroupOf (normalizer (S0 : Set G))).IsSubnormal :=
    (assembly_isSubnormal_iff_subgroupOf hFN).1 hsub
  let e : F ≃* F.subgroupOf (normalizer (S0 : Set G)) := (Subgroup.subgroupOfEquivOfLe hFN).symm
  intro L hL
  have hL' : CFSG.IsPComponent 2 (L.map e.toMonoidHom) := isPComponent_map_of_isPComponent 2 e hL
  have hL'' := CatalogueBPrimeJoin.pComponent_extend_subnormal 2 _ hF'sub _ hL'
  have hcomp := hB S0 hS0 hS02 _ ((isTwoPComponent_iff_isPComponent _).2 hL'')
  have hle : (L.map e.toMonoidHom).map (F.subgroupOf (normalizer (S0 : Set G))).subtype ≤
      F.subgroupOf (normalizer (S0 : Set G)) := map_subtype_le _
  have hcompF := isComponentOf_of_le hcomp hle le_top
  rw [isComponentOf_iff_isComponent_subgroupOf hle] at hcompF
  have hsub_eq : ((L.map e.toMonoidHom).map
      (F.subgroupOf (normalizer (S0 : Set G))).subtype).subgroupOf
        (F.subgroupOf (normalizer (S0 : Set G))) = L.map e.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [hsub_eq] at hcompF
  exact (isComponent_map_iff e L).1 hcompF

end Bridges

section Normalizers

variable {G : Type*} [Group G]

theorem mem_normalizer_iSup {ι : Type*} {K : ι → Subgroup G} {g : G}
    (h : ∀ j, g ∈ normalizer (K j : Set G)) : g ∈ normalizer ((⨆ j, K j : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conjSub_le ?_ ?_
  · rw [conjSub, Subgroup.map_iSup]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_of_mem_normalizer (h j))
  · rw [conjSub, Subgroup.map_iSup]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_of_mem_normalizer (inv_mem (h j)))

theorem mem_normalizer_inf {X Y : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hY : g ∈ normalizer (Y : Set G)) : g ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hX hY ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hX, hY]


end Normalizers


end CFSG.LocalAnalysis.ComponentInitial
