module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_isPGroup_sup {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) :
    ∃ c ∈ H, IsPGroup 2 ↥(A ⊔ conjSub c B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A' : Subgroup H := A.subgroupOf H
  let B' : Subgroup H := B.subgroupOf H
  have hA' : IsPGroup 2 ↥A' :=
    hA.of_surjective (Subgroup.subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAH).symm.surjective
  have hB' : IsPGroup 2 ↥B' :=
    hB.of_surjective (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  obtain ⟨Q₁, hQ₁⟩ := hA'.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hB'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q₂ Q₁
  refine ⟨(g : G), g.2, ?_⟩
  set T : Subgroup G := (Q₁ : Subgroup H).map H.subtype with hT
  have hTp : IsPGroup 2 ↥T :=
    Q₁.isPGroup'.of_surjective ((Q₁ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).toMonoidHom ((Q₁ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).surjective
  refine hTp.to_le (sup_le ?_ ?_)
  · intro a ha
    have : (⟨a, hAH ha⟩ : H) ∈ A' := ha
    exact ⟨_, hQ₁ this, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hbB' : (⟨b, hBH hb⟩ : H) ∈ B' := hb
    have h1 := hQ₂ hbB'
    have h2 : (Q₂ : Subgroup H).map (MulAut.conj g).toMonoidHom = (Q₁ : Subgroup H) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      ext x
      simp [Subgroup.pointwise_smul_def]
    have h3 : (MulAut.conj g) ⟨b, hBH hb⟩ ∈ (Q₁ : Subgroup H) := by
      rw [← h2]
      exact ⟨_, h1, rfl⟩
    exact ⟨_, h3, rfl⟩

end Sylow

section Orbit


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.normalizer_eq_centralizer (h : BadStd8 Ω K J S R T W z t) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  refine le_antisymm (fun n hn => ?_)
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz)
  have h1 := hs.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]


end Orbit

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
