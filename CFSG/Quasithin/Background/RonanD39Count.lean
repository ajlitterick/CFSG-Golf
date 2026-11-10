module

public import CFSG.Quasithin.Background.RonanD39Block

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Quasithin.Z391 CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem exists_fixed_ne_one_of_isPGroup [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {B : Subgroup Γ}
    (hB : IsPGroup 2 ↥B) {M : Subgroup Q} (hM : ∀ b ∈ B, ∀ m ∈ M, b • m ∈ M) (hne : M ≠ ⊥) :
    ∃ m ∈ M, m ≠ 1 ∧ ∀ b ∈ B, b • m = m := by
  let _ : MulAction ↥B ↥M :=
    { smul := fun b m => ⟨(b : Γ) • (m : Q), hM b b.2 m m.2⟩
      one_smul := fun m => Subtype.ext (one_smul Γ (m : Q))
      mul_smul := fun a b m => Subtype.ext (mul_smul (a : Γ) (b : Γ) (m : Q)) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 ↥M := (isPGroup_two_of_sq_eq_one hQ).to_subgroup M
  have hdvd : 2 ∣ Nat.card ↥M := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hM2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : ↥M) ∈ MulAction.fixedPoints ↥B ↥M := fun b =>
    Subtype.ext (smul_one (b : Γ))
  obtain ⟨m, hm, hne1⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥M hdvd h1
  refine ⟨m, m.2, fun h => hne1 (Subtype.ext h.symm), fun b hb => ?_⟩
  exact congrArg Subtype.val (hm ⟨b, hb⟩)


end CFSG.Quasithin.RonanD39
