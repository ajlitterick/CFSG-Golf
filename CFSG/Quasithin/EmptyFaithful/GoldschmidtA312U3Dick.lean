module

public import CFSG.Quasithin.EmptyFaithful.A38c15Gl2
public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.A38c15 CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem charP_of_card_sq (hF : Nat.card F = p ^ 2) : CharP F p := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])

omit [Finite F] in
theorem uniData (hF : Nat.card F = p ^ 2) : UnitaryFieldData p 1 F :=
  ⟨Fact.out, le_rfl, by simpa using hF⟩

theorem two_ne_zero_of_card_sq (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : (2 : F) ≠ 0 := by
  have := charP_of_card_sq (p := p) hF
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem exists_su2_equiv (hF : Nat.card F = p ^ 2) :
    Nonempty (SL(2, ZMod p) ≃* ↥(StatedSU 2 (p ^ 1) F)) := by
  have := charP_of_card_sq (p := p) hF
  have hK : Nat.card F = (p ^ 1) ^ 2 := by simpa using hF
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p) (f := 1) hK
  have hfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p 1) = p := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    simp
  exact ⟨(CFSG.ClassicalModels.specialLinearFieldEquiv (fieldEquivZMod hfix).symm (Fin 2)).trans e⟩


end CFSG.Quasithin.A312U3
