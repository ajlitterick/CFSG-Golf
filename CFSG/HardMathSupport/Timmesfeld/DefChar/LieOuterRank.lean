module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwistedAC
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.HardMathSupport.Timmesfeld.Coordinator (LieOuterRank)

theorem lieOuterRank_proved : LieOuterRank :=
  lieOuterRank_of_families fun k => by
    cases k with
    | A => exact lieOuterRankFam_A
    | twistedA => exact lieOuterRankFamTwistedA
    | B => exact lieOuterRankFamB
    | C => exact lieOuterRankFamC
    | D => exact lieOuterRankFamD
    | twistedD => exact lieOuterRankFamTwistedD
    | E6 => exact lieOuterRankFamE6
    | E7 => exact lieOuterRankFamE7
    | E8 => exact lieOuterRankFamE8
    | F4 => exact lieOuterRankFamF4
    | G2 => exact lieOuterRankFamG2
    | twistedE6 => exact lieOuterRankFamTwistedE6
    | trialityD4 => exact lieOuterRankFamTrialityD4
    | suzuki => exact lieOuterRankFamSuzuki
    | reeG2 => exact lieOuterRankFamReeG2
    | reeF4 => exact lieOuterRankFamReeF4
    | tits => exact lieOuterRankFamTits

end CFSG.HardMathSupport.Timmesfeld.DefChar
