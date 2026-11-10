module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.RouteD.TypeCChain
public import CFSG.ClassicalInvolution.RouteD.TypeF4Closure

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair longBlock
  shortBlock planeGroup stdPlane isHyperbolicPlane_stdPlane IsHyperbolicPlane)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section PerfectLift

theorem commutator_self_le {H : Type*} [Group H] (S : Subgroup H) : ⁅S, S⁆ ≤ S :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem exists_perfect_lift {Y : Type*} [Group Y] {O : Subgroup Y} [O.Normal]
    (hO : O ≤ Subgroup.center Y) {S : Subgroup (Y ⧸ O)} (hS : S ≤ ⁅S, S⁆) :
    ∃ A : Subgroup Y, A ≤ ⁅A, A⁆ ∧ A.map (QuotientGroup.mk' O) = S := by
  let π := QuotientGroup.mk' O
  let T : Subgroup Y := S.comap π
  have hmapT : T.map π = S :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) S
  have hmapA : (⁅T, T⁆).map π = S := by
    rw [Subgroup.map_commutator, hmapT]
    exact le_antisymm (commutator_self_le S) hS
  refine ⟨⁅T, T⁆, ?_, hmapA⟩
  have hTA : T ≤ ⁅T, T⁆ ⊔ O := by
    intro a ha
    have : π a ∈ (⁅T, T⁆).map π := hmapA ▸ hmapT ▸ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    have hmem : b⁻¹ * a ∈ O := QuotientGroup.eq.mp hba
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hmem)
  have hZc : ∀ z ∈ O, ∀ h ∈ (⊤ : Subgroup Y), z * h = h * z := fun z hz h _ =>
    (Subgroup.mem_center_iff.mp (hO hz) h).symm
  refine Subgroup.commutator_le.mpr fun t₁ ht₁ t₂ ht₂ => ?_
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ :=
    exists_mul_of_mem_sup_central (H := ⊤) (A := ⁅T, T⁆) le_top hZc (hTA ht₁)
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ :=
    exists_mul_of_mem_sup_central (H := ⊤) (A := ⁅T, T⁆) le_top hZc (hTA ht₂)
  rw [commutator_mul_of_central (H := ⊤) trivial trivial trivial (hZc z₁ hz₁) (hZc z₂ hz₂)]
  exact Subgroup.commutator_mem_commutator ha₁ ha₂

end PerfectLift

section Nodes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem locImg_map_subtype {Ω : Set (Subgroup G)} {x : G} (A : Subgroup ↥(locLayer Ω x)) :
    locImg Ω x (A.map (locLayer Ω x).subtype) =
      A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))) := by
  unfold locImg
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (locLayer Ω x).subtype_injective]


end Nodes

end CFSG.ClassicalInvolution.RouteD
