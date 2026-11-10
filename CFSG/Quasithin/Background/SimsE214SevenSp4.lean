module

public import CFSG.Quasithin.Background.SimsE214SevenSec
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB42Sp4Ident

public section

namespace CFSG.Quasithin.SimsE2

namespace E214S

open CFSG.Quasithin CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Rep

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem finrank_eq_four_of_card_lt {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hcard : Nat.card M < 2 ^ (8 * f)) :
    Module.finrank (EndRing (repOf π)) M = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  have hfd : f ≤ S.card * d := by
    have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    have h2 : 2 * f ≤ 2 * (S.card * d) := by
      calc 2 * f ≤ S.card * (2 * d) := h
        _ = 2 * (S.card * d) := by ring
    omega
  have hM : Nat.card M = 2 ^ (d * 4 ^ S.card) := by
    rw [natCard_eq_pow_finrank (ρ := repOf π), hDcard, hdimW, ← pow_mul]
  rw [hM] at hcard
  have h1 : d * 4 ^ S.card < 8 * f := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hcard
  rw [hdimW]
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  by_contra hne
  have hs2 : 2 ≤ S.card := by
    by_contra h
    have h' : S.card = 1 := by omega
    rw [h', pow_one] at hne
    exact hne rfl
  have h8 := Nat.mul_le_mul_left d (eight_mul_le_four_pow hs2)
  nlinarith


end Rep


end E214S

end CFSG.Quasithin.SimsE2
