module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSub

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem sing_iff {v : Fin 64} :
    (caseC3Word Z u m y x v ∈ e1RBar Z u m y x ∧
      caseC3Word Z u m y x v * caseC3Word Z u m y x v = 1 ∧ caseC3Word Z u m y x v ≠ 1 ∧
      caseC3Word Z u m y x v ≠ caseC3Word Z u m y x 40) ↔ e1Sing v := by
  rw [hb.caseC3Word_mem_e1RBar_iff, hb.caseC3Word_mul_self_eq_one_iff, Ne,
    hb.caseC3Word_eq_one_iff, Ne, hb.caseC3Word_inj]
  rfl


theorem not_genuine_of_mem_e1EBar {s : G ⧸ Z} (hs : s ∈ e1EBar Z u m y x) (hs1 : s ≠ 1)
    (hsz : s ≠ caseC3Word Z u m y x 40) :
    ¬ CaseC3.Genuine Z s ∧ ¬ CaseC3.Genuine Z (s * caseC3Word Z u m y x 40) := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  obtain ⟨gf, gef, -, -, hlab⟩ := hb.exists_e1Gen
  have h := e1Gen_e1E gf gef v hv (fun h => hs1 (by rw [h, caseC3Word_zero]))
    (fun h => hsz (by rw [h]))
  rw [hb.caseC3Word_mul, hlab, hlab, h.1, h.2]
  exact ⟨Bool.false_ne_true, Bool.false_ne_true⟩

theorem mem_e1EBar_of_typeD (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) {s : G ⧸ Z}
    (hs : s ∈ e1RBar Z u m y x) (hss : s * s = 1) (hgen : ¬ CaseC3.Genuine Z s) :
    s ∈ e1EBar Z u m y x := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  rw [hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen
  exact hb.caseC3Word_mem_e1EBar_iff.mpr
    (e1E_of_e1R_typeD v hv (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hgen)

theorem mem_e1EBar_of_typeD' (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) {s : G ⧸ Z}
    (hs : s ∈ S.map (QuotientGroup.mk' Z)) (hss : s * s = 1) (hgen : ¬ CaseC3.Genuine Z s)
    (hgen' : ¬ CaseC3.Genuine Z (s * caseC3Word Z u m y x 40)) : s ∈ e1EBar Z u m y x := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [hb.caseC3Word_mul, hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen'
  rw [hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen
  exact hb.caseC3Word_mem_e1EBar_iff.mpr
    (e1E_of_typeD v (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hgen hgen')

theorem eq_e1EBar_of_typeD (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    {A : Subgroup (G ⧸ Z)} (hAS : A ≤ S.map (QuotientGroup.mk' Z))
    (hzA : caseC3Word Z u m y x 40 ∈ A) (hcard : 8 ≤ Nat.card A) (hsq : ∀ s ∈ A, s * s = 1)
    (hgen : ∀ s ∈ A, s ≠ 1 → s ≠ caseC3Word Z u m y x 40 → ¬ CaseC3.Genuine Z s) :
    A = e1EBar Z u m y x := by
  have hzz : caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 = 1 :=
    hb.caseC3Word_mul_self_eq_one_iff.mpr c3Mul_forty_forty
  refine Subgroup.eq_of_le_of_card_ge (fun s hs => ?_) (hb.card_e1EBar ▸ hcard)
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  by_cases hsz : s = caseC3Word Z u m y x 40
  · rw [hsz]
    exact hb.forty_mem_e1EBar
  refine hb.mem_e1EBar_of_typeD' htype (hAS hs) (hsq s hs) (hgen s hs hs1 hsz)
    (hgen _ (A.mul_mem hs hzA) (fun h => hsz ?_) (fun h => hs1 ?_))
  · rw [show s = s * caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 by
      rw [mul_assoc, hzz, mul_one], h, one_mul]
  · rw [show s = s * caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 by
      rw [mul_assoc, hzz, mul_one], h, hzz]


theorem pow_four_eq_one {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z)) : s ^ 4 = 1 := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hb.caseC3Word_mul, hb.caseC3Word_mul,
    c3_exponent_four, caseC3Word_zero]

theorem mul_self_PQ_iff {v : Fin 64} :
    (caseC3Word Z u m y x v * caseC3Word Z u m y x v ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ∧
      caseC3Word Z u m y x v * caseC3Word Z u m y x v ≠ 1 ∧
      ¬ CaseC3.Genuine Z (caseC3Word Z u m y x v * caseC3Word Z u m y x v)) ↔
    e1PQ (c3Mul v v) := by
  rw [hb.caseC3Word_mul, hb.caseC3Word_mem_sup_iff, Ne, hb.caseC3Word_eq_one_iff]
  constructor
  · rintro ⟨h4, h0, hg⟩
    exact ⟨h4, h0, fun h => hg ((hb.genuine_even_iff (by omega)).mpr (Or.inr h))⟩
  · rintro ⟨h4, h0, hg⟩
    refine ⟨h4, h0, fun h => ?_⟩
    rcases (hb.genuine_even_iff (by omega)).mp h with h' | h'
    exacts [h0 h', hg h']

theorem mem_bot_of_mul_self {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z))
    (hW : s * s ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) (h1 : s * s ≠ 1)
    (hgen : ¬ CaseC3.Genuine Z (s * s)) :
    s ∈ T.map (QuotientGroup.mk' Z) ∧ s ∉ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  have h2 := e1PQ_mul_self v (hb.mul_self_PQ_iff.mp ⟨hW, h1, hgen⟩)
  rw [hb.caseC3Word_mem_bot_iff, hb.caseC3Word_mem_sup_iff]
  omega


end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
