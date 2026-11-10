module

public import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.GMS

open CFSG CFSG.Blueprint.NativeSporadic CFSG.Monster.Existence

variable {G : Type} [Group G]

theorem GMSLeechCentralizer.of_isTwoBCentralizer {z : G} (hz : orderOf z = 2)
    (h : IsTwoBCentralizer z) : GMSLeechCentralizer z := by
  obtain ⟨hQ, hcard, hcen, ⟨e⟩, -, -⟩ := h
  refine ⟨hz, hQ, hcard,
    ⟨(MonoidHom.ofClass e).comp (QuotientGroup.mk' _), ?_, ?_⟩, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨c, rfl⟩
  · ext c
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · intro c hc
    have hcG : (c : G) ∈ Subgroup.centralizer
        (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hc q hq
      simpa using congrArg Subtype.val this
    obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.mp (hcen hcG)
    rw [show c = q from Subtype.ext hqc.symm]
    exact hq

theorem GMSDoubleF2Centralizer.of_isTwoACentralizer {a : G} (ha : orderOf a = 2)
    (hB : IsSimpleGroup B) {d₀ : B} (hd₀ : orderOf d₀ = 2) (h : IsTwoACentralizer a) :
    GMSDoubleF2Centralizer d₀ a := by
  obtain ⟨hperf, hcenter, ⟨e⟩⟩ := h
  refine ⟨ha, Group.isPerfect_def.mp hperf, B, inferInstance,
    (MonoidHom.ofClass e).comp (QuotientGroup.mk' _), ?_, ?_, hB, d₀, hd₀, ⟨MulEquiv.refl _⟩⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨c, rfl⟩
  have hker : ((MonoidHom.ofClass e).comp (QuotientGroup.mk' (Subgroup.center
      (Subgroup.centralizer ({a} : Set G))))).ker =
        Subgroup.center (Subgroup.centralizer ({a} : Set G)) := by
    ext c
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hker]
  exact hcenter


end CFSG.Monster.GMS
