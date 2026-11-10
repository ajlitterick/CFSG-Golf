module

public import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

section MacWilliams

variable {F : Type} [Group F]

private theorem isElemAbelian_map_subtype {S : Subgroup F} {E' : Subgroup S} (h : IsElemAbelian 2 E') :
    IsElemAbelian 2 (E'.map S.subtype) := by
  obtain ⟨hcomm, hexp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have hab : (⟨a', ha'⟩ : E') * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ :=
      hcomm.is_comm.comm _ _
    have h1 : a' * b' = b' * a' := congrArg Subtype.val hab
    apply Subtype.ext
    show (a : F) * (b : F) = (b : F) * (a : F)
    rw [← ha, ← hb]
    exact congrArg Subtype.val h1
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : x' ^ 2 = 1 := hexp x' hx'
    simpa using congrArg Subtype.val h1

theorem fourGenerated_of_sylow [Finite F] (S : Sylow 2 F)
    (h : ∀ P : Subgroup F, P ≤ (S : Subgroup F) →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P) :
    ∀ P : Subgroup F, IsPGroup 2 P →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P := by
  classical
  intro P hP
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F S T
  have hT : (T : Subgroup F) = (S : Subgroup F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hP'S : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup F) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyT : y ∈ (S : Subgroup F).map (MulAut.conj g).toMonoidHom := hT ▸ hPT hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hyT
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom s) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hs
  obtain ⟨X, hX4, hXcl⟩ := h _ hP'S
  refine ⟨X.image (fun x => g * x * g⁻¹), Finset.card_image_le.trans hX4, ?_⟩
  have hcoe : ((X.image (fun x => g * x * g⁻¹) : Finset F) : Set F) =
      (MulAut.conj g).toMonoidHom '' (X : Set F) := by
    rw [Finset.coe_image]
    rfl
  rw [hcoe, ← MonoidHom.map_closure, hXcl, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e]
    exact hy
  · intro hx
    exact ⟨x, hx, by group⟩

theorem exists_normal_elemAbelian_eight_of_not_fourGenerated [Finite F]
    (h : ¬ ∀ P : Subgroup F, IsPGroup 2 P →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P) (S : Sylow 2 F) :
    ∃ E : Subgroup F, E ≤ (S : Subgroup F) ∧ (E.subgroupOf (S : Subgroup F)).Normal ∧
      IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  by_contra hne
  apply h
  have hE : ∀ E' : Subgroup (S : Subgroup F), E'.Normal → IsElemAbelian 2 E' →
      Nat.card E' ≠ 8 := by
    intro E' hN hEA hc
    apply hne
    refine ⟨E'.map (S : Subgroup F).subtype, Subgroup.map_subtype_le E', ?_,
      isElemAbelian_map_subtype hEA, ?_⟩
    · have : (E'.map (S : Subgroup F).subtype).subgroupOf (S : Subgroup F) = E' :=
        Subgroup.comap_map_eq_self_of_injective (S : Subgroup F).subtype_injective E'
      rw [this]
      exact hN
    · rw [Subgroup.card_map_of_injective (S : Subgroup F).subtype_injective]
      exact hc
  have hall := CFSG.Milestones.cls_connectivity_macwilliams_four_generator
    (S : Subgroup F) S.isPGroup' hE
  refine fourGenerated_of_sylow S fun P hPS => ?_
  obtain ⟨X, hX4, hXcl⟩ := hall (P.subgroupOf (S : Subgroup F))
  refine ⟨X.image (S : Subgroup F).subtype, Finset.card_image_le.trans hX4, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXcl]
  exact Subgroup.map_subgroupOf_eq_of_le hPS

end MacWilliams

section UniqueInvolution

variable {G : Type*} [Group G]

private theorem conj_mem_of_normal_subgroupOf {S E : Subgroup G} (hE : (E.subgroupOf S).Normal)
    {q e : G} (hq : q ∈ S) (he : e ∈ E) (heS : e ∈ S) : q * e * q⁻¹ ∈ E := by
  have h := hE.conj_mem ⟨e, heS⟩ (Subgroup.mem_subgroupOf.mpr he) ⟨q, hq⟩
  exact Subgroup.mem_subgroupOf.mp h


end UniqueInvolution

end CFSG.ClassicalInvolution
