module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisPerfect
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

theorem two_dvd_natCard (F : Type) [Field F] [Finite F] [CharP F 2] : 2 ∣ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.pos.ne'

theorem pCore_sl2_charTwo (F : Type) [Field F] [Finite F] [CharP F 2] :
    CFSG.pCore 2 (SL₂ F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 (SL₂ F) with hNdef
  have hN : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hNn : N.Normal := CFSG.pCore_normal
  have hcard : 2 ∣ Nat.card F := two_dvd_natCard F
  have hdvd : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun]
    exact hcard.trans (dvd_pow_self _ (by simp))
  have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints N (Fin 2 → F) := fun n => smul_zero _
  obtain ⟨w, hw, hw0⟩ :=
    hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hdvd h0
  have hfix : ∀ n ∈ N, ∀ v : Fin 2 → F, (n : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
    intro n hn v
    by_cases hv : v = 0
    · rw [hv, Matrix.mulVec_zero]
    · obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq (Ne.symm hw0) hv
      have hconj : M⁻¹ * n * M ∈ N := by
        have := hNn.conj_mem n hn M⁻¹
        rwa [inv_inv] at this
      have h1 : ((M⁻¹ * n * M : SL₂ F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w :=
        (MulAction.mem_fixedPoints.mp hw) ⟨_, hconj⟩
      have h2 : (n : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) =
          (M : Matrix (Fin 2) (Fin 2) F) * ((M⁻¹ * n * M : SL₂ F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        congr 1
        rw [mul_assoc, mul_inv_cancel_left]
      rw [← hM, Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h1]
  refine eq_bot_iff.mpr fun n hn => ?_
  rw [Subgroup.mem_bot]
  have hmat : (n : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Matrix.ext_of_mulVec_single fun i => by rw [hfix n hn, Matrix.one_mulVec]
  exact Subtype.ext hmat


end CFSG.Quasithin.SimsG4
