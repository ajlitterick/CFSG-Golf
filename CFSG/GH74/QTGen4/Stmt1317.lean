module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.GH74.QTGen4.Perfect.Final

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin

theorem pCore_two_quotient_eq_bot_1317 {H : Type} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set M : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMN : M ≤ N := le_sSup ⟨inferInstance, hMp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hMN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy


end CFSG.GH74.QTGen4
