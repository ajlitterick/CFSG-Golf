module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_orderOf_eq_of_dvd_add_one (K : Type) [Field K] [Finite K] {L : Type} [Field L]
    [Algebra K L] [IsAlgClosed L] {N : ℕ} (hN : N ∣ Nat.card K + 1) :
    ∃ ζ : Lˣ, orderOf ζ = N ∧ ζ ^ (Nat.card K + 1) = 1 := by
  classical
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero ((N : ℕ) : L) := ⟨by
    obtain ⟨m, hm⟩ := hN
    intro hN0
    have h1 : ((Nat.card K + 1 : ℕ) : L) = 0 := by rw [hm, Nat.cast_mul, hN0, zero_mul]
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1⟩
  have hNpos : N ≠ 0 := fun h0 => by
    rw [h0] at hN
    exact absurd (Nat.eq_zero_of_zero_dvd hN) (by omega)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  set ζu : Lˣ := (hζ.isUnit hNpos).unit with hζu
  have hζu' : IsPrimitiveRoot ζu N :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  refine ⟨ζu, hζu'.eq_orderOf.symm, ?_⟩
  obtain ⟨m, hm⟩ := hN
  rw [hm, pow_mul, hζu'.pow_eq_one, one_pow]

section Twisted


end Twisted

section Family


end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
