module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {p : ℕ} {S : Type*} [Group S]

theorem commute_or_eq_of_isQuasisimple {L M : Subgroup S} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hML : M ≤ L) (hMn : ∀ g ∈ L, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    (∀ m ∈ M, ∀ l ∈ L, l * m = m * l) ∨ M = L := by
  obtain ⟨hperf, hsimple⟩ := hL
  have hN : (M.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff hML).2 fun h k hh hk => hMn k hk h hh
  have hNq : ((M.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    ((M.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    intro m hm l hl
    have hc : (⟨m, hML hm⟩ : ↥L) ∈ Subgroup.center ↥L := h hm
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨l, hl⟩)
  · right
    have h1 : M.subgroupOf L ⊔ Subgroup.center ↥L = ⊤ := by
      have h2 : (M.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
          (⊤ : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
        rw [h, Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      rw [Subgroup.map_eq_map_iff, QuotientGroup.ker_mk'] at h2
      simpa using h2
    have h3 := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h1 inferInstance
    rw [hperf] at h3
    exact le_antisymm hML (Subgroup.subgroupOf_eq_top.1 (top_le_iff.1 h3))

theorem commutator_eq_self_of_commutator_eq_top {L : Subgroup S} (h : commutator ↥L = ⊤) :
    ⁅L, L⁆ = L := by
  have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ L.subtype
  rw [← commutator_def, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm

theorem gLAPPrimeCoreOf_eq_bot_of_isQuasisimple [Finite S] (hp : p.Prime) {C L : Subgroup S}
    (hLC : L ≤ C) (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hpL : p ∣ Nat.card L) (hCL : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L : Set S))) :
    GLAPPrimeCoreOf p C = ⊥ := by
  refine gLAPPrimeCoreOf_eq_bot_of_perfect hp hLC hLn
    (commutator_eq_self_of_commutator_eq_top hL.1) ?_ hCL
  intro M hML hMn hcop m hm l hl
  rcases commute_or_eq_of_isQuasisimple hL hML hMn with h | h
  · exact h m hm l hl
  · subst h
    exact absurd hpL ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)

@[expose] def PConstrainedShape (p : ℕ) (C : Subgroup S) : Prop :=
  ∃ Q : Subgroup S, Q ≤ C ∧ (∀ g ∈ C, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧ IsPGroup p Q ∧
    C ⊓ Subgroup.centralizer (Q : Set S) ≤ Q


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
