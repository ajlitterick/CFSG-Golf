module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual
public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTD4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

theorem muResidualG2D4_proved (p f : ℕ) [Fact p.Prime] : MuResidualG2D4 p f where
  g2 hp2 hq X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact g2_omegaStarNbr_nonempty M hS.hyp hp2 hq hne
  trialityD4 hp2 hq X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact td4_omegaStarNbr_nonempty M hS.hyp hp2 hq hne


end MuTab

variable {p f : ℕ} [Fact p.Prime]

theorem ih8MuTableSect_of_d4Star (hD4 : Ih8D4Star p f) : Ih8MuTableSect p f :=
  ih8MuTableSect_of_g2d4 hD4 (MuTab.muResidualG2D4_proved p f)

theorem ih8MuTable_of_d4Star (hD4 : Ih8D4Star p f) : Ih8MuTable p f :=
  ih8MuTable_of_g2d4 hD4 (MuTab.muResidualG2D4_proved p f)

end CFSG.ClassicalInvolution.Asc77
