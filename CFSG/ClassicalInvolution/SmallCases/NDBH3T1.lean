module

public import CFSG.ClassicalInvolution.SmallCases.NDBE9Final
import CFSG.ClassicalInvolution.SmallCases.NDBG3Proved
import CFSG.ClassicalInvolution.Asc77.AscBSE8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]


theorem bootNoG2D4Twin_proved : BootNoG2D4Twin p f := by
  intro G _ _ _ K z hS hT D i hi
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  obtain ⟨T, hTΩ, hTK, hTz⟩ : ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z := hT
  have hb : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    rcases hi with h' | h'
    · rw [show C.D.tag i = .G2 from h'] at h
      exact absurd h.1 (by decide)
    · rw [show C.D.tag i = .trialityD4 from h'] at h
      exact absurd h.1 (by decide)
  have h3 : 3 ≤ C.D.card := NDBG.three_le_card_of_twin C hb hTΩ hTK hTz
  rcases hi with hG2 | hD4
  · exact bootNoG2Twin_proved G K z hS D i hG2 h3
  · exact NDBG.false_of_trialityD4_of_card (C := C) (Asc77.BSC.noFuzzyFrame hS) hD4 h3

theorem noDataBootD_of_narrowA (hA : NoAllA1Narrow p f) : SmallConn.NoDataBootD p f :=
  noDataBootD_of_residualsX (noAllA1_of_narrow hA) noG2D4Twin_proved
    (exoticNoTwinFrames_of_spin (exoticFrameSpin_proved p f))

theorem bootNoTripleD_of_narrowA (hA : NoAllA1Narrow p f) : Disconnected.BootNoTripleD p f :=
  bootNoTripleD_of_coverXW (bootShapeCoverX_of_residuals
      ⟨bootNoAllA1_of_narrow hA, bootNoG2D4Twin_proved, Asc77.BSC.BSD.bootNoM3Twin,
        Asc77.BSC.BSD.bootNoManyTwins
          (Asc77.BSC.BSE.bootNoManyTwinsD4_of_five bootNoD4FiveComp_proved)⟩)
    (exoticNoTwinFrames_of_spin (exoticFrameSpin_proved p f))

end CFSG.ClassicalInvolution.NDB
