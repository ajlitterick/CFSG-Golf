module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Sets

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tqMembers_conj (hΩ : ConjInvariant Ω) (g c : G) :
    tqMembers Ω (g * c * g⁻¹) = conjSub g '' tqMembers Ω c := by
  ext K'
  constructor
  · intro hK'
    refine ⟨conjSub g⁻¹ K', ⟨hΩ g⁻¹ K' hK'.1, ?_⟩, conjSub_conjSub_inv g K'⟩
    have h := trivialOnQuot_conjSub hK'.2 g⁻¹
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rwa [e] at h
  · rintro ⟨K, hK, rfl⟩
    exact ⟨hΩ g K hK.1, trivialOnQuot_conjSub hK.2 g⟩

theorem exactFamily_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactFamily Ω (g * c * g⁻¹) = conjSub g '' exactFamily Ω c := by
  ext K'
  constructor
  · rintro ⟨K, hK, rfl⟩
    rw [tqMembers_conj hΩ] at hK
    obtain ⟨K₀, hK₀, rfl⟩ := hK
    exact ⟨exactCore c K₀, ⟨K₀, hK₀, rfl⟩, (exactCore_conjSub g c K₀).symm⟩
  · rintro ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    refine ⟨conjSub g K, ?_, (exactCore_conjSub g c K).symm⟩
    rw [tqMembers_conj hΩ]
    exact ⟨K, hK, rfl⟩

theorem exactLayer_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactLayer Ω (g * c * g⁻¹) = conjSub g (exactLayer Ω c) := by
  rw [exactLayer_eq_iSup, exactLayer_eq_iSup, exactFamily_conj hΩ, iSup_image]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun K' => ?_
  rw [Subgroup.map_iSup]

end Sets

section OddQuotient

variable {G : Type} [Group G]

@[expose] noncomputable def centralizerConj (g c : G) :
    ↥(Subgroup.centralizer ({c} : Set G)) ≃* ↥(Subgroup.centralizer ({g * c * g⁻¹} : Set G)) :=
  (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (conjSub_centralizer_singleton g c))

theorem coe_centralizerConj (g c : G) (x : ↥(Subgroup.centralizer ({c} : Set G))) :
    ((centralizerConj g c x : ↥(Subgroup.centralizer ({g * c * g⁻¹} : Set G))) : G) =
      g * (x : G) * g⁻¹ := rfl

@[expose] noncomputable def oddQuotConj (g c : G) : OddQuot c ≃* OddQuot (g * c * g⁻¹) :=
  QuotientGroup.congr (componentClassificationOddCore _) (componentClassificationOddCore _)
    (centralizerConj g c) (OddCore.equiv_invariant (centralizerConj g c))

theorem oddQuotConj_oddQuotMk (g c : G) (x : ↥(Subgroup.centralizer ({c} : Set G))) :
    oddQuotConj g c (oddQuotMk c x) = oddQuotMk (g * c * g⁻¹) (centralizerConj g c x) := rfl

theorem map_centralizerConj_subgroupOf (g c : G) (K : Subgroup G) :
    (K.subgroupOf (Subgroup.centralizer ({c} : Set G))).map (centralizerConj g c).toMonoidHom =
      (conjSub g K).subgroupOf (Subgroup.centralizer ({g * c * g⁻¹} : Set G)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_conjSub hx
  · intro hy
    have hyC : (y : G) ∈ conjSub g (Subgroup.centralizer ({c} : Set G)) := by
      rw [conjSub_centralizer_singleton]
      exact y.2
    have hxC : g⁻¹ * (y : G) * g ∈ Subgroup.centralizer ({c} : Set G) := mem_conjSub_iff.mp hyC
    refine ⟨⟨g⁻¹ * (y : G) * g, hxC⟩, mem_conjSub_iff.mp hy, Subtype.ext ?_⟩
    show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
    group

theorem map_oddQuotConj_modOdd (g c : G) (K : Subgroup G) :
    (modOdd c K).map (oddQuotConj g c).toMonoidHom = modOdd (g * c * g⁻¹) (conjSub g K) := by
  unfold modOdd
  rw [Subgroup.map_map]
  have hcomm : (oddQuotConj g c).toMonoidHom.comp (oddQuotMk c) =
      (oddQuotMk (g * c * g⁻¹)).comp (centralizerConj g c).toMonoidHom := rfl
  rw [hcomm, ← Subgroup.map_map, map_centralizerConj_subgroupOf]

end OddQuotient

section ImagesConj


end ImagesConj

section LieTransport


end LieTransport

section DecompositionTransport


end DecompositionTransport

end CFSG.ClassicalInvolution.Asc77.ExactLayer
