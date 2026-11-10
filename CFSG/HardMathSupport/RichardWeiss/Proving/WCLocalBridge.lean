module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.Timmesfeld75


theorem exists_normal_complement_of_le_center {C : Type*} [Group C] [Finite C] {p : ℕ}
    [Fact p.Prime] (P : Sylow p C) (hP : (P : Subgroup C) ≤ Subgroup.center C) :
    ∃ N : Subgroup C, N.Normal ∧ (P : Subgroup C).IsComplement' N := by
  have hN : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_center_iff.1 (hP hh)) g).symm
  exact ⟨(MonoidHom.transferSylow P hN).ker, inferInstance,
    (MonoidHom.ker_transferSylow_isComplement' P hN).symm⟩

theorem galoisField_two_one_eq_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  by_contra h
  push Not at h
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h3 : ({0, 1, c} : Finset (GaloisField 2 1)).card = 3 :=
    Finset.card_eq_three.2 ⟨0, 1, c, zero_ne_one, fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, c} : Finset (GaloisField 2 1))
  rw [h3, ← Nat.card_eq_fintype_card, hcard] at hle
  omega


end CFSG.HardMathSupport.RichardWeiss.Proving
