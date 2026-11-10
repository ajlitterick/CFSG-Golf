module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

section Hypotheses

variable {G : Type} [Group G]

@[expose] def FFNotStronglyClosed (b : G) : Prop :=
  ∃ x ∈ Subgroup.zpowers b, ∃ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) ∧
    g * x * g⁻¹ ∉ Subgroup.zpowers b

@[expose] def FFCentCyclicSylow (L : Subgroup G) : Prop :=
  ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)),
    IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (L : Set G)))

@[expose] def FFHypA5 [Finite G] (b : G) : Prop :=
  ∀ B : Subgroup G, B ≤ Subgroup.centralizer ({b} : Set G) → CFSG.Open.IsElemAbelian 3 B →
    (∃ T : Subgroup G, T ≤ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      B ≤ Subgroup.normalizer (T : Set G)) →
    Nat.card B = 3 ^ localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ ¬ B ≤ Subgroup.centralizer (T : Set G)

@[expose] def FFStandardJ (b : G) (J : Subgroup G) : Prop :=
  J ≤ Subgroup.centralizer ({b} : Set G) ∧
    CFSG.IsComponent (J.subgroupOf (Subgroup.centralizer ({b} : Set G))) ∧
    ∀ K : Subgroup ↥(Subgroup.centralizer ({b} : Set G)), CFSG.IsComponent K →
      3 ∣ Nat.card K → K = J.subgroupOf (Subgroup.centralizer ({b} : Set G))

theorem FFNotWeaklyClosed.notStronglyClosed [Finite G] {b : G} (h : FFNotWeaklyClosed b) :
    FFNotStronglyClosed b := by
  obtain ⟨g, hle, hne⟩ := h
  refine ⟨b, Subgroup.mem_zpowers b, g⁻¹, ?_, fun hmem => hne ?_⟩
  · apply hle
    refine ⟨b, Subgroup.mem_zpowers b, ?_⟩
    simp [MulAut.conj_apply]
  · have hle' : conjugate (Subgroup.zpowers b) g ≤ Subgroup.zpowers b := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : (MulAut.conj g⁻¹).toMonoidHom (b ^ k) = (g⁻¹ * b * g⁻¹⁻¹) ^ k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        simpa only [inv_inv] using (conj_zpow (a := g⁻¹) (i := k) (b := b)).symm
      rw [hk]
      exact Subgroup.zpow_mem _ hmem k
    refine Subgroup.eq_of_le_of_card_ge hle' ?_
    rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

end Hypotheses


end CFSG.RankThree.PartTwo.Sec21
