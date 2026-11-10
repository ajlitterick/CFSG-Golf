module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TightEnd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Member

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

@[expose] def TwinExclusion : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ClassicalCommuteBelow F → ClassicalQuasisimple F →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z →
      ¬ (Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) → False


section Assembly

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem center_trivial_of_simple [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) :
    ∀ x : F, (∀ y : F, x * y = y * x) → x = 1 := by
  intro x hx
  have hnormal : (Subgroup.center F).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · have : x ∈ Subgroup.center F := Subgroup.mem_center_iff.mpr fun y => (hx y).symm
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center F := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm


theorem false_of_classical2A7 [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)
    (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) : False := by
  by_cases ht : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)
  · exact TightSetting.false_of_goldschmidt hnab GS
      ⟨⟨hK, ht⟩, center_trivial_of_simple hnab, IH, P1⟩
  · exact TW F hnab IH P1 K z hK ht

theorem false_of_witness [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)
    (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion) {z : F} (hz : orderOf z = 2)
    {K : Subgroup F} (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer ({z} : Set F)))
    (hw : A7Witness K) : False := by
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK hw
  exact false_of_classical2A7 hnab IH P1 GS TW hL


end Assembly

end CFSG.ClassicalInvolution.Hat2A7
