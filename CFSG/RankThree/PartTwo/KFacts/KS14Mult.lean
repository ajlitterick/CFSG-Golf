module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.KFacts.KS18Mult
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

theorem not_sq_dvd_of_coprime_six {N : ℕ} (hN : N = 95040 ∨ N = 2520 ∨ N = 443520) {p : ℕ}
    (hp : p.Prime) (hp6 : Nat.Coprime 6 p) : ¬ p ^ 2 ∣ N := by
  have hcheck : ∀ q < 667, Nat.Coprime 6 q → 2 ≤ q →
      ¬ q ^ 2 ∣ 95040 ∧ ¬ q ^ 2 ∣ 2520 ∧ ¬ q ^ 2 ∣ 443520 := by
    decide +kernel
  intro hd
  have hN0 : 0 < N := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hle := Nat.le_of_dvd hN0 hd
  have hp667 : p < 667 := by
    by_contra h
    have : 667 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    rcases hN with rfl | rfl | rfl <;> omega
  obtain ⟨h1, h2, h3⟩ := hcheck p hp667 hp6 hp.two_le
  rcases hN with rfl | rfl | rfl
  · exact h1 hd
  · exact h2 hd
  · exact h3 hd

theorem ks18Mult_sporadic (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : Group.IsPerfect X) (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    (hS : Nonempty (X ⧸ Z ≃* NativeSporadic.M12) ∨
      Nonempty (X ⧸ Z ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ⧸ Z ≃* NativeSporadic.M22)) : Z = ⊥ := by
  have hN : Nat.card (X ⧸ Z) = 95040 ∨ Nat.card (X ⧸ Z) = 2520 ∨ Nat.card (X ⧸ Z) = 443520 := by
    rcases hS with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine Or.inl ?_
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
      exact le_antisymm ((Nat.card_le_card_of_surjective _
        CFSG.Sporadic.Bridge.M12.toNative_surjective).trans hle)
        CFSG.Sporadic.Bridge.M12.le_card_native
    · refine Or.inr (Or.inl ?_)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · refine Or.inr (Or.inr ?_)
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
      exact le_antisymm ((Nat.card_le_card_of_surjective _
        CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
        CFSG.Sporadic.Bridge.M22.le_card_native
  refine eq_bot_of_isPerfect_of_not_sq_dvd hZc fun p hp hpZ => ?_
  have hp6 : Nat.Coprime 6 p := Nat.Coprime.coprime_dvd_right hpZ hcop
  exact not_sq_dvd_of_coprime_six hN hp hp6

theorem card_dvd_griess_of_le_center {X S : Type} [Group X] [Group S] (hX : Group.IsPerfect X)
    {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X) (e : X ⧸ Z ≃* S) :
    Nat.card Z ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  have := hX
  let q : X →* S := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq (hker.le.trans hZc)
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq (hker.le.trans hZc))


end CFSG.RankThree.PartTwo.KFacts.KS14
