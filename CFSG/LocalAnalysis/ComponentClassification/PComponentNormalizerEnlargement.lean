module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G]

theorem subgroupOf_isSubnormal_of_le {L C A : Subgroup G} (hCA : C ≤ A)
    (h : (L.subgroupOf A).IsSubnormal) : (L.subgroupOf C).IsSubnormal := by
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := h.subgroupOf
  have hcomap : L.subgroupOf C = ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).comap
      (Subgroup.subgroupOfEquivOfLe hCA).symm.toMonoidHom := by
    ext x
    rfl
  rw [hcomap]
  exact h1.comap _

theorem subgroupOf_isSubnormal_iff {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (hC : (C.subgroupOf A).IsSubnormal) :
    (L.subgroupOf A).IsSubnormal ↔ (L.subgroupOf C).IsSubnormal := by
  refine ⟨subgroupOf_isSubnormal_of_le hCA, fun h => ?_⟩
  have hcomap : (L.subgroupOf A).subgroupOf (C.subgroupOf A) =
      (L.subgroupOf C).comap (Subgroup.subgroupOfEquivOfLe hCA).toMonoidHom := by
    ext x
    rfl
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := by
    rw [hcomap]
    exact h.comap _
  exact Subgroup.IsSubnormal.trans (fun x hx => hLC hx) h1 hC

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have hfwd : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) v).1 hv
    have hwc := Subgroup.mem_centralizer_iff.1 hc _ hw
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [hwc]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hfwd g hg c, fun hc => ?_⟩
  have h := hfwd g⁻¹ (inv_mem hg) _ hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem pComponent_subgroupOf_iff_of_subnormal {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (hC : (C.subgroupOf A).IsSubnormal) :
    IsPComponent p (L.subgroupOf A) ↔ IsPComponent p (L.subgroupOf C) := by
  rw [pComponent_subgroupOf_iff p L A (hLC.trans hCA), pComponent_subgroupOf_iff p L C hLC,
    subgroupOf_isSubnormal_iff hLC hCA hC]

theorem pComponent_subgroupOf_of_le {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (h : IsPComponent p (L.subgroupOf A)) : IsPComponent p (L.subgroupOf C) := by
  rw [pComponent_subgroupOf_iff p L A (hLC.trans hCA)] at h
  rw [pComponent_subgroupOf_iff p L C hLC]
  exact ⟨subgroupOf_isSubnormal_of_le hCA h.1, h.2⟩


end CFSG.ComponentClassification.CatalogueBPrimeJoin
