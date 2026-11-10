module

public import CFSG.RankThree.PartTwo.Census.CarrierCases
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.RankThree.PartTwo.Census.Carrier.ReeG2One
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartTwo.Census

open TauCeti

theorem carrierCases433_of_spin
    (g2Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Excluded433 (.lie ⟨.G2 q, hv⟩))
    (trialityD4Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      Excluded433 (.lie ⟨.trialityD4 q, hv⟩))
    (reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), Excluded433 (.lie ⟨.reeF4 m, hv⟩))
    (tits : ∀ hv : LieTypeIndex.tits.Valid, Excluded433 (.lie ⟨.tits, hv⟩)) :
    CarrierCases433 :=
  { sp8Two := bridgeSp8Two,
    sp6Four := bridgeSp6Four,
    omega8PlusTwo := bridgeOmega8PlusTwo,
    omega8MinusTwo := bridgeOmega8MinusTwo,
    b3Two := excluded433_B_three_two,
    g2Even := g2Even,
    g2Three := excluded433_G2_three,
    g2Prime := excluded433_G2_prime,
    trialityD4Even := trialityD4Even,
    reeG2One := excluded433_reeG2_one,
    reeF4 := reeF4,
    tits := tits }

end CFSG.RankThree.PartTwo.Census
