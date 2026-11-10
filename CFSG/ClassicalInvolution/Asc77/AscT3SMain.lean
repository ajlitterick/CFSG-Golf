module

public import CFSG.ClassicalInvolution.Asc77.AscT3SOrb
public import CFSG.ClassicalInvolution.Asc77.AscT3SC3
public import CFSG.ClassicalInvolution.Asc77.AscT3RFinal

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem c20_3_of_hyp51 (hH : Res20_7Hyp51 p f) : C20_3 p f := by
  intro G _ _ _ K K' J S R R' W V z t d
  have hex : Hex20 (CoreAssembly.conjClass K) K J W := ⟨d.late_JW, d.late_hW⟩
  exact d.concl20_3_of_mod hex
    (res20_7NoC3_of_hyp51 hH G K K' J S R R' W V z t d (d.concl20_4_of_hex hex))

theorem res20_3_of_hyp51 (hH : Res20_7Hyp51 p f) : Res20_3 p f :=
  res20_3_of_c20_3 (c20_3_of_hyp51 hH)


theorem res20_3_of_hyp51At (hH : Res20_7Hyp51At p f) : Res20_3 p f :=
  res20_3_of_hyp51 (res20_7Hyp51_of_at hH)

theorem res20_7_of_hyp51At (hH : Res20_7Hyp51At p f) : Res20_7 p f :=
  res20_7_of_hyp51 (res20_7Hyp51_of_at hH)


end CFSG.ClassicalInvolution.Asc77.T3CII
