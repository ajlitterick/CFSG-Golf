module

public import CFSG.LocalAnalysis.LargeEvenClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] noncomputable def twoLocalPRank (prime : ℕ) (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] : ℕ :=
  twoLocalPrimeRank prime Ambient


theorem pRank_mono {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) {Small Large : Subgroup Ambient} (hle : Small ≤ Large) :
    pRank prime Small ≤ pRank prime Large := CFSG.SectionRank.pRank_mono hprime hle


theorem pRank_le_twoLocalPRank {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) :
    pRank prime Local ≤ twoLocalPRank prime Ambient := by
  apply le_csSup
  · refine ⟨Nat.card Ambient, ?_⟩
    rintro rank ⟨OtherLocal, _, hrank⟩
    rw [← hrank]
    exact pRank_le_card hprime OtherLocal
  · exact ⟨Local, hlocal, rfl⟩


end CFSG.LargeEvenClassification.Helpers
