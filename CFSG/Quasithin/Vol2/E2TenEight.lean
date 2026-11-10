module

public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.Blueprint.Multiplier

namespace E2

open scoped commutatorElement

theorem two_le_of_isPSp4 {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) : 2 ≤ n := by
  obtain ⟨⟨-, hf, -, hne⟩, -⟩ := h
  by_contra hn
  have h1 : n = 1 := by omega
  subst h1
  exact hne rfl

theorem isSimpleGroup_of_isPSp4 {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) :
    IsSimpleGroup Y := by
  have hn := two_le_of_isPSp4 h
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
    (Or.inl (Or.inr h4))
  exact MulEquiv.isSimpleGroup eK

theorem psp_row_param {n : ℕ} (hn : 2 ≤ n) :
    5 ≤ 2 ^ n ∨ 2 ^ n = 4 ∨ (2 ^ n = 2 ∧ 4 ≤ 2) ∨ (2 ^ n = 3 ∧ 3 ≤ 2) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · exact Or.inr (Or.inl rfl)
  · left
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3

theorem commutator_eq_top_of_isPSp4
    {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) :
    commutator Y = ⊤ :=
  (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row h
    (psp_row_param (two_le_of_isPSp4 h))).1

theorem center_eq_bot_of_isPSp4
    {L Y : Type} [Group L] [Group Y] [Group.IsPerfect L] {n : ℕ}
    (hY : IsPSp4 2 n Y) (e : L ⧸ Subgroup.center L ≃* Y) : Subgroup.center L = ⊥ := by
  have hn := two_le_of_isPSp4 hY
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hY
    (psp_row_param hn)
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hg : genericOrders .PSp 2 2 n = (1, 1) := by
    show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)]
  have he : exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  have : Subsingleton (generic .PSp 2 2 n × exceptional .PSp 2 2 n) := by
    unfold generic exceptional
    rw [hg, he]
    show Subsingleton ((Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)))
    infer_instance
  have : Subsingleton (CFSG.Open.griessHopfMultiplier Y) := eM.toEquiv.subsingleton
  obtain ⟨φ, hφ⟩ := exists_surjective_center e
  exact eq_bot_of_surjective_subsingleton φ hφ

namespace Pair


end Pair

end E2


end CFSG.Quasithin
