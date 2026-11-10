module

public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Final

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.RankThree.PerfectCover

theorem card_ker_dvd_hopfMultiplier {R S : Type} [Group R] [Finite R] [Group.IsPerfect R]
    [Group S] [Finite S] (p : R →* S) (hp : Function.Surjective p)
    (hC : p.ker ≤ Subgroup.center R) : Nat.card p.ker ∣ Nat.card (hopfMultiplier S) := by
  haveI : Group.IsPerfect S := Group.IsPerfect.ofSurjective hp
  obtain ⟨-, h, -, -, -, -, ⟨e, -⟩⟩ := perfect_central_kernel_quotient_of_hopf_multiplier p hp hC
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _


end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
